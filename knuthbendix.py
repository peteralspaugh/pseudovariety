#!/usr/bin/env python
# coding: utf-8

# In[5]:


# String rewriting functions and the Knuth-Bendix completion algorithm
# Algorithms can be found in String Rewriting Systems by Book & Otto, Springer-Verlag 1993
# Peter Alspaugh, July 2025


# In[6]:


# Remove all duplicates from a list
def remduplicates(list):
    for i in list:
        count = 0
        for j in list:
            if i==j:
                count += 1
        if count>1:
            for k in range(1,count):
                list.remove(i)
    return list

# Remove all trivial rules x -> x to keep system Noetherian
def remtrivial(list):
    for i in list:
        if i[0] == i[1]:
            list.remove(i)
    return list

# Executes both remduplicates() and remtrivial() on a list
def simplifyrules(list):
    list = remtrivial(remduplicates(list))
    return list


# In[7]:


def sortorder(list, order = None, shortlex_alph = None):
    if order == None:
        return shortlex(list, shortlex_alph)


# In[8]:


# Sorts a list by length-lexicographic (shortlex) order: length first, then alphabetical order (default) or another alphabet order if one is provided
def shortlex(list, order = None):
    if order == None:
        return sorted(list, key = lambda x: (len(x), x))
    else:
        rank = {c: i for i, c in enumerate(order)}
        return sorted(list, key = lambda x: (len(x), [rank[c] for c in x]))


# In[9]:


# Determine if input word is reduced according to input set of rewriting rule pairs
def isreduced(rules, word):
    for r in rules:
        if r[0] in word:
            return False
    return True


# In[10]:


# Given an input set of rewriting rule pairs, reduce an input word to an irreducible word according to those rules
# Starts from the left of the word and the left of the rules list and rewrites subwords in that order
def reduce(rules, word):
    rules = simplifyrules(rules)
    while not(isreduced(rules,word)):
        for r in rules:
            if r[0] in word:
                pos = word.index(r[0])
                word = word[:pos]+r[1]+word[pos+len(r[0]):]
    return word


# In[11]:


# Determine if rule set is normalized, meaning all right hand sides are irreducible and left hand sides are irreducible with respect to all other rules
def isnormalized(rules):
    for r in rules:
        rules_sans = rules.copy()
        rules_sans.remove(r)
        if not(isreduced(rules_sans,r[0]) and isreduced(rules,r[1])):
            return False
    return True


# In[12]:


# Returns a normalized rule set with the same Thue congruence as the input rule set
def normalize(rules, order = None, order_alph = None):
    rules = simplifyrules(rules)
    while not(isnormalized(rules)):
        for r in rules:
            rules_sans = rules.copy()
            rules_sans.remove(r)
            r[1] = reduce(rules_sans,r[1])
            rules = simplifyrules(rules)
        for r in rules:
            rules_sans = rules.copy()
            rules_sans.remove(r)
            new = sortorder([reduce(rules_sans,r[0]),r[1]],order,order_alph)
            new.reverse()
            rules[rules.index(r)] = new
            rules = simplifyrules(rules)
    return rules


# In[13]:


def overlaps(u,v):
    list = []
    for i in range(1,min(len(u),len(v))):
        if u[len(u)-i:] == v[:i]:
            list.append(u[:len(u)-i]+v)
    for i in range(1,min(len(u),len(v))):
        if v[len(v)-i:] == u[:i]:
            list.append(v[:len(v)-i]+u)
    return list


# In[14]:


# Tests if string rewriting system is locally confluent
# Does this by overlapping the left-hand sides of all pairs of rewriting rules and checking if they reduce to the same irreducible
def islocallyconfluent(rules):
    for r in rules:
        for s in rules:
            list = overlaps(r[0],s[0])
            if r[0] in s[0]:
                list.append(s[0])
            if s[0] in r[0]:
                list.append(r[0])
            for i in list:
                reductions = []
                irreducibles = []
                for j in range(0,len(i)):
                    if i[j:j+len(r[0])] == r[0]:
                        reduc = i[:j]+r[1]+i[j+len(r[0]):]
                        reductions.append(reduc)
                    if i[j:j+len(s[0])] == s[0]:
                        reduc = i[:j]+s[1]+i[j+len(s[0]):]
                        reductions.append(reduc)
                for j in reductions:
                    irreducibles.append(reduce(rules,j))
                if len(remduplicates(irreducibles)) != 1:
                    return False
    return True


# In[32]:


# Returns a complete and normalized rewriting system with the same Thue congruence as the rule set
# Does this by adding in a rule y -> z whenever there is a string x such that x -> y, y -> z, and z < y according to the given order
def knuthbendix(rules, order = None, order_alph = None, printrules = False):
    alreadyfound = rules
    count = 0
    while not(islocallyconfluent(rules)):
        count += 1
        rules = normalize(rules)
        rules = simplifyrules(rules)
        newrules = []
        for r in rules:
            for s in rules:
                list = overlaps(r[0],s[0])
                if r[0] in s[0]:
                    list.append(s[0])
                if s[0] in r[0]:
                    list.append(r[0])
                for i in list:
                    reductions = []
                    irreducibles = []
                    for j in range(0,len(i)):
                        if i[j:j+len(r[0])] == r[0]:
                            reduc = i[:j]+r[1]+i[j+len(r[0]):]
                            reductions.append(reduc)
                        if i[j:j+len(s[0])] == s[0]:
                            reduc = i[:j]+s[1]+i[j+len(s[0]):]
                            reductions.append(reduc)
                    for j in reductions:
                        irreducibles.append(reduce(rules,j))
                    irreducibles = remduplicates(irreducibles)
                    irreducibles = sortorder(irreducibles,order,order_alph)
                    if len(irreducibles) != 1:
                        for k in sortorder(irreducibles,order,order_alph):
                            if irreducibles.index(k) != 0:
                                newrules.append([k,irreducibles[0]])
        for i in newrules:
            if not(i in alreadyfound):
                rules.append(i)
        alreadyfound.extend(newrules)
        if printrules == True:
            print("(",count,") ",rules,"\n")
    rules = normalize(rules)
    rules = simplifyrules(rules)
    return rules

