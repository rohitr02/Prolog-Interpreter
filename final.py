from prolog_structures import Constant, Rule, RuleBody, Term, Function, Variable, Atom, Number
from typing import List
from functools import reduce

import sys
import random

class Not_unifiable(Exception):
	pass

'''
Please read prolog_structures.py for data structures
that represent Prolog terms, rules, and goals.
'''
class Interpreter:
	def __init__(self):
		pass

	'''
	Example
	occurs_check (v, t) where v is of type Variable, t is of type Term.
	occurs_check (v, t) returns true if the Prolog Variable v occurs in t.
	Please see the lecture note Control in Prolog to revisit the concept of
	occurs-check.
	'''
	def occurs_check (self, v : Variable, t : Term) -> bool:
		if isinstance(t, Variable):
			return v == t
		elif isinstance(t, Function):
			for t in t.terms:
				if self.occurs_check(v, t):
					return True
			return False
		return False


	'''
	Problem 1
	variables_of_term (t) where t is of type Term.
	variables_of_clause (c) where c is of type Rule.

	The function should return the Variables contained in a term or a rule
	using Python set.

	The result must be saved in a Python set. The type of each element (a Prolog Variable)
	in the set is Variable.
	'''
	def variables_of_term (self, t : Term) -> set :
		s1 = set()
		s2 = set()
		if isinstance(t, Variable):
			s1 = set([t])
		elif isinstance(t, Function):
			for t in t.terms:
				s2 = s2.union(self.variables_of_term(t))
		elif isinstance(t, Constant):
			pass
		return s1.union(s2)

	def variables_of_clause (self, c : Rule) -> set:
		s1 = set()
		for term in c.head.terms:
			s1 = s1.union(self.variables_of_term(term))
		s2 = set()
		for term in c.body.terms:
			s2 = s2.union(self.variables_of_term(term))
		return s2.union(s1)


	'''
	Problem 2
	substitute_in_term (s, t) where s is of type dictionary and t is of type Term
	substitute_in_clause (s, t) where s is of type dictionary and c is of type Rule,

	The value of type dict should be a Python dictionary whose keys are of type Variable
	and values are of type Term. It is a map from variables to terms.

	The function should return t_ obtained by applying substitution s to t.

	Please use Python dictionary to represent a subsititution map.
	'''
	def substitute_in_term (self, s : dict, t : Term) -> Term:
		if isinstance(t, Function):
			new_terms = []
			for term in t.terms:
				new_terms.append(self.substitute_in_term(s, term))
			return Function(t.relation, new_terms)
		elif isinstance(t, Variable):
			if t in s.keys(): return s[t]
			else: return t
		else: return t

	def substitute_in_clause (self, s : dict, c : Rule) -> Rule:
		new_head = self.substitute_in_term(s, c.head)
		new_body = []
		for term in c.body.terms:
			new_body += [self.substitute_in_term(s, term)]
		return Rule(new_head, RuleBody(new_body))

	'''
	Problem 3
	unify (t1, t2) where t1 is of type term and t2 is of type Term.
	The function should return a substitution map of type dict,
	which is a unifier of the given terms. You may find the pseudocode
	of unify in the lecture note Control in Prolog useful.

	The function should raise the exception raise Not_unfifiable (),
	if the given terms are not unifiable.

	Please use Python dictionary to represent a subsititution map.
	'''

	def unify_helper (self, X : Term, Y : Term, theta : dict) -> dict:
		X = self.substitute_in_term(theta, X)
		Y = self.substitute_in_term(theta, Y)
		# Case 1: X is a variable that does not occur in Y:
		if isinstance(X, Variable) and not self.occurs_check(X, Y):
			# replace X with Y in the substitution terms of dict_map and add X/Y to dict_nap
			for key, value in theta.items():
				theta[key] = self.substitute_in_term({X:Y}, value)
			theta[X] = Y
			return theta
		# Case 2: Y is a variable that does not occur in X:
		elif isinstance(Y, Variable) and not self.occurs_check(Y, X):
			# replace Y with X in the substitution terms of dict_map and add Y/X to dict_nap
			for key, value in theta.items():
				theta[key] = self.substitute_in_term({Y:X}, value)
			theta[Y] = X
			return theta
		# Case 3: X and Y are constants:
		elif isinstance(X, Constant) and isinstance(Y, Constant):
			if X == Y:
				return theta
			else:
				raise Not_unifiable()
		# Case 4: X and Y are identical variables:
		elif isinstance(X, Variable) and isinstance(Y, Variable):
			if X == Y:
				return theta
			else:
				raise Not_unifiable()
		# Case 5: X and Y are functions:
		elif isinstance(X, Function) and isinstance(Y, Function):
			# return (fold_left (fun 𝜃 (X,Y) -> unify(X,Y,𝜃)) 𝜃 [(X1,Y1),...,(Xn,Yn)])
			if X.relation == Y.relation and len(X.terms) == len(Y.terms):
				for term1, term2 in zip(X.terms, Y.terms):
					theta.update(self.unify_helper(term1, term2, theta))
				return theta
			else:
				raise Not_unifiable()
		else:
			raise Not_unifiable()


	def unify (self, t1 : Term, t2 : Term) -> dict:
		return self.unify_helper(t1, t2, {})


	fresh_counter = 0
	def fresh(self) -> Variable:
		self.fresh_counter += 1
		return Variable("_G" + str(self.fresh_counter))
	def freshen(self, c: Rule) -> Rule:
		c_vars = self.variables_of_clause(c)
		theta = {}
		for c_var in c_vars:
			theta[c_var] = self.fresh()

		return self.substitute_in_clause(theta, c)


	'''
	Problem 4
	Following the Abstract interpreter pseudocode in the lecture note Control in Prolog to implement
	a nondeterministic Prolog interpreter.

	nondet_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of Terms (results), which is an instance of the original goal and is
	a logical consequence of the program. See the tests cases (in src/main.py) as examples.
	'''
	def nondet_query (self, program : List[Rule], pgoal : List[Term]) -> List[Term]:
		resolvent = pgoal[:]
		while resolvent != []:
			A = resolvent[random.randint(0, len(resolvent) - 1)]
			A_prime = self.freshen(program[random.randint(0, len(program) - 1)])
			theta = {}
			try: theta = self.unify(A, A_prime.head)
			except Not_unifiable: break
			else:
				resolvent += [term for term in A_prime.body.terms]
				resolvent.remove(A)

				pgoal = [self.substitute_in_term(theta, t) for t in pgoal]
				resolvent = [self.substitute_in_term(theta, t) for t in resolvent]

		if resolvent == []: return pgoal
		else: return self.nondet_query(program, pgoal)


	'''
	Challenge Problem

	det_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of term lists (results). Each of these results is
	an instance of the original goal and is a logical consequence of the program.
	If the given goal is not a logical consequence of the program, then the result
	is an empty list. See the test cases (in src/main.py) as examples.
	'''
	def det_query (self, program : List[Rule], pgoal : List[Term]) -> List[List[Term]]:
		# initialize resolvent (which is a list from the goal)
		resolvent = pgoal[:]
		# initialize solutions as an empty list
		solutions = []
		# call dfs with resolvent, goal, and solutions
		return self.dfs(program, resolvent, pgoal, solutions)

	# follow dfs pseudocode in the piazza post
	def dfs (self, program : List[Rule], resolvent : List[Term], goal : List[Term], solutions : List[List[Term]]) -> List[List[Term]]:
		if resolvent == []:
			solutions.append(goal)
		else:
			chosen_goal = resolvent[0]
			for rule in program:
				try:
					self.unify(chosen_goal, rule.head)
				except Not_unifiable: continue
				else:
					rule = self.freshen(rule)
					theta = self.unify(chosen_goal, rule.head)
					new_resolvent = resolvent[1:]
					new_goal = goal[:]

					new_resolvent += [term for term in rule.body.terms]
					new_resolvent = [self.substitute_in_term(theta, t) for t in new_resolvent]
					new_goal = [self.substitute_in_term(theta, t) for t in goal]

					self.dfs(program, new_resolvent, new_goal, solutions)
		return solutions
	
