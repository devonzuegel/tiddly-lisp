import sys, re, traceback, operator


#### Symbol, Env classes ###############################################################

Symbol = str

# An environment: a dict of { 'var': val } pairs, with an outer Env.
class Env(dict):
  def __init__(self, params = (), args = (), outer = None):
    self.update(zip(params, args))
    self.outer = outer

  # Find the innermost Env where `var` appears.
  def find(self, var):
    # Note that the environment doesn't distinguish between variable and
    # procedure names. Indeed, tiddlylisp treats user-defined procedures and
    # variables in the same way: a procedure is a variable which just happens
    # to take the value of a lambda expression as its value.
    if var in self:     return self
    else:               return self.outer.find(var)


# Add some built-in procedures and variables to the environment.
def add_globals(env):
  # NOTE: easy to add more built-in procedures to tiddlylisp.
  env.update({
    '+':  operator.add,
    '-':  operator.sub,
    '*':  operator.mul,
    '/':  operator.div,
    '>':  operator.gt,
    '<':  operator.lt,
    '>=': operator.ge,
    '<=': operator.le,
    '=':  operator.eq
  })
  env.update({ 'True': True, 'False': False })
  return env


global_env = add_globals(Env())
isa        = isinstance



#### Eval ##############################################################################

# Evaluate an expression in an environment.
def eval(x, env = global_env):
  if isa(x, Symbol):                      # variable reference
    return env.find(x)[x]
  elif not isa(x, list):                  # constant literal
    return x
  elif x[0] == 'quote' or x[0] == 'q':    # (quote exp) or (q exp)
    (_, exp) = x
    return exp
  elif x[0] == 'atom?':                   # (atom? exp)
    (_, exp) = x
    return not isa(eval(exp, env), list)
  elif x[0] == 'eq?':                     # (eq? exp1 exp2)
    (_, exp1, exp2) = x
    v1 = eval(exp1, env)
    v2 = eval(exp2, env)
    return (not isa(v1, list)) and (v1 == v2)
  elif x[0] == 'car':                     # (car exp)
    (_, exp) = x
    return eval(exp, env)[0]
  elif x[0] == 'cdr':                     # (cdr exp)
    (_, exp) = x
    return eval(exp, env)[1:]
  elif x[0] == 'cons':                    # (cons exp1 exp2)
    (_, exp1, exp2) = x
    mylist = [ eval(exp1, env) ]
    return mylist + eval(exp2, env)
  elif x[0] == 'cond':                    # (cond (p1 e1) ... (pn en))
    for (p, e) in x[1:]:
      if eval(p, env):
        return eval(e, env)
    return []
  elif x[0] == 'null?':                   # (null? exp)
    (_, exp) = x
    return eval(exp, env) == []
  elif x[0] == 'if':                      # (if test conseq alt)
    (_, test, conseq, alt) = x
    result = conseq if eval(test, env) else alt
    return eval(result, env)
  elif x[0] == 'set!':                    # (set! var exp)
    (_, var, exp) = x
    env.find(var)[var] = eval(exp, env)
  elif x[0] == 'define':                  # (define var exp)
    (_, var, exp) = x
    env[var] = eval(exp, env)
  elif x[0] == 'lambda':                  # (lambda (var*) exp)
    (_, vars, exp) = x
    return lambda *args: eval(exp, Env(vars, args, env))
    # Lambda expressions evaluate to the appropriate anonymous Python function, with a new
    # environment modified by the addition of the appropriate variable keys and their values.
  elif x[0] == 'begin':                   # (begin exp*)
    for exp in x[1:]:
      val = eval(exp, env)
    return val

  else:                                   # (proc exp*)
    exps = [eval(exp, env) for exp in x]
    proc = exps.pop(0)
    if (len(exps) == 1) and (proc == operator.add or proc == operator.sub):
      exps = [0] + exps
    while len(exps) > 2:
      val1, val2, rest = exps[0], exps[1], exps[2:]
      new_first_val = proc(val1, val2)
      exps = [new_first_val] + rest
    return proc(*exps)



#### Parsing ###########################################################################

# Parse a Lisp expression from a string.
def parse(s):
  return read_from(tokenize(s))

# Convert string into list of tokens.
def tokenize(s):
  replacements = {  '(':' ( ',  ')':' ) ' }
  for (orig, replcmt) in replacements.iteritems():
    s = s.replace(orig, replcmt)
  tokens = s.split()
  result = []
  str_so_far, open_parens = '', False
  for token in tokens:
    if open_parens:
      str_so_far += " %s" % token
      if token[-1] == '"':
        result += [ str_so_far ]
        open_parens, str_so_far = False, ''
    elif token[0] == '"':
      str_so_far, open_parens = token, True
    else:
      result += [ token ]
  return result



# Read an expression form a sequence of tokens.
def read_from(tokens):
  if len(tokens) == 0:
    raise SyntaxError('Unexpected EOF while reading.')
  token = tokens.pop(0)
  if token == '(':
    L = []
    while tokens[0] != ')':
      L.append(read_from(tokens))
    tokens.pop(0)  # Pop off ')'
    return L
  elif token == ')':
    raise SyntaxError('Unexpected )')
  else:
    return atom(token)


# Numbers become numbers; every other token is a symbol.
def atom(token):
  try:      return int(token)
  except ValueError:
    try:               return float(token)
    except ValueError: return Symbol(token)


# Convert a Python object back into a Lisp-readable string.
def to_string(exp):
  if not isa(exp, list):  return str(exp)
  else:                   return "(%s)" % ' '.join(map(to_string, exp))



#### Loading ###########################################################################

##
# Load the tiddlylisp program in filename, execute it, and start the repl. If an error
# occurs, execution stops, and we are left in the repl.  Note that load copes with
# multi-line tiddlylisp code by merging lines until the number of opening and closing
# parentheses match.
def load(filename):
  print "Loading and executing '%s'." % filename
  f = open(filename, 'r')
  program = f.readlines()
  f.close()
  rps = running_paren_sums(program)
  full_line = ''
  for (paren_sum, program_line) in zip(rps, program):
    program_line = program_line.strip()
    full_line   += "%s " % program_line
    if (paren_sum == 0) and (full_line.strip() != ''):
      try:
        val = eval(parse(full_line))
        if val is not None: print to_string(val)
      except:
        handle_error()
        print "\nThe line in which the error occurred:\n"
        break
      full_line = ''
  repl()


##
# Map the lines in the list program to a list whose entries contain a running sum of the
# per-line difference between the number of '(' parentheses & the number of ')' parentheses.
def running_paren_sums(program):
  count_open_parens = lambda line: line.count('(') - line.count(')')
  paren_counts      = map(count_open_parens, program)
  rps   = []
  total = 0
  for paren_count in paren_counts:
    total += paren_count
    rps.append(total)
  return rps



#### Repl ##############################################################################

# A prompt-read-eval-print loop.
def repl(prompt = '> '):
  while True:
    try:
      parsed_input = parse(raw_input(prompt))
      val = eval(parsed_input)
      if val is not None:
        print to_string(val)
    except KeyboardInterrupt:
      print "\nExiting tiddlylisp... Bye!\n"
      sys.exit()
    except:  # TODO: improve me!
      handle_error()


#### Error handling ####################################################################

# Error handling for both the repl and load.
def handle_error():
  print "An error occurred. Here's the Python stack trace:\n"
  traceback.print_exc()



#### On startup ########################################################################

if __name__ == '__main__':
  if len(sys.argv) > 1:  load(sys.argv[1])
  else:                  repl()

