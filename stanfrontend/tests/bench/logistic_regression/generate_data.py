import json
from numpy import *
import scipy.special


alpha = round(random.normal(0, .1), 3)
beta = round(random.normal(0, .1), 3)

params = {'alpha': alpha, 'beta': beta}

print(json.dumps(params))
f = open("params.json", 'w')
print(json.dumps(params), file=f)

x = [round(random.normal(0, .1), 3) for i in range(200)]
y = []
for i in range(len(x)):
    p = scipy.special.expit(alpha + beta * x[i])
    y.append(random.binomial(1, p))

data = {'x': x, 'y': y}

f = open("data.json", 'w')
print(json.dumps(data))
print(json.dumps(data), file=f)
