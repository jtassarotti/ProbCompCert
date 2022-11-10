import json
from numpy import *


alpha = round(random.normal(0, 1), 3)
beta = round(random.normal(0, 1), 3)
sigma = round(max(0.0, random.normal(1, .1)), 3)

params = {'alpha': alpha, 'beta': beta, 'sigma': sigma}

print(json.dumps(params))
f = open("params.json", 'w')
print(json.dumps(params), file=f)

x = [round(random.normal(0, 1), 2) for i in range(200)]
y = []
for i in range(len(x)):
    y.append(round(random.normal(alpha + beta * x[i], sigma), 4))

data = {'x': x, 'y': y}

f = open("data.json", 'w')
print(json.dumps(data))
print(json.dumps(data), file=f)
