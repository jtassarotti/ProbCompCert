import json
from numpy import *

hyper_sigma = 1

mu = round(random.normal(0, 3), 3)
gamma = round(random.normal(0, 3), 3)
sigma = round(max(0.0, random.normal(1, .1)), 3)

num_classes = 2

alpha = [round(random.normal(mu, hyper_sigma), 1) for x in range(num_classes)]
beta = [round(random.normal(gamma, hyper_sigma), 1) for x in range(num_classes)]

params = {'mu': mu, 'gamma': gamma, 'alpha': alpha, 'beta': beta, 'sigma': sigma}

print(json.dumps(params))
f = open("params.json", 'w')
print(json.dumps(params), file=f)

x = [round(random.normal(0, 1), 2) for i in range(200)]
cls = [random.randint(1, 3) for i in range(200)]
y = []
for i in range(len(x)):
    y.append(round(random.normal(alpha[cls[i]-1] + beta[cls[i]-1] * x[i], sigma), 4))

data = {'x': x, 'y': y, 'class': cls}

f = open("data.json", 'w')
print(json.dumps(data))
print(json.dumps(data), file=f)
