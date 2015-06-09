# analysis.py
# -----------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).



######################
# ANALYSIS QUESTIONS #
######################

# For the Bayes' Nets, query variables, and evidence given in the
# website, return the set of variables that can be ignored when
# performing inference.
# Do not include evidence variables.

def question5a():
    ignoredVariables = ['W','G']
    # Example solution : ignoredVariables = ['E', 'G'] (order does not matter so ['G','E'] is also the same)
    return ignoredVariables

def question5b():
    ignoredVariables = ['A', 'H', 'I']
    return ignoredVariables

def question5c():
    ignoredVariables = ['X1', 'X2', 'X3', 'X4', 'X5', 'X6', 'Y1', 'Y2', 'Y3', 'Y4', 'Y5', 'Y6', 'Y7', 'Y8', 'Y12', 'Y13', 'Y14']
    return ignoredVariables


