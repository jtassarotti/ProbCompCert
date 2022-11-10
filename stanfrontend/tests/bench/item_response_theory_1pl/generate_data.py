import json
from numpy import *
import scipy.special


# 25 questions
# 25 students

num_students = 15
num_questions = 15

alpha = [round(random.normal(0, 10), 3) for i in range(num_students)]
beta = [round(random.normal(0, 10), 3) for i in range(num_questions)]

params = {'alpha': alpha, 'beta': beta}

print(json.dumps(params))
f = open("params.json", 'w')
print(json.dumps(params), file=f)

jj = []
kk = []
y = []

cntr = 0
for k in range(num_questions):
    for j in range(num_students):
        jj.append(j + 1)
        kk.append(k + 1)

        y.append(random.binomial(1, scipy.special.expit(alpha[j] - beta[k])))

data = {'jj': jj, 'kk' : kk, 'y': y}

f = open("data.json", 'w')
print(json.dumps(data))
print(json.dumps(data), file=f)
