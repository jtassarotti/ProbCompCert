import json
from numpy import *

mu = round(random.uniform(0, 1), 3)

params = {'mu': mu}

print(json.dumps(params))
f = open("params.json", 'w')
print(json.dumps(params), file=f)

flips = [random.binomial(1, mu) for i in range(100)]

data = {'flips': flips}

f = open("data.json", 'w')
print(json.dumps(data))
print(json.dumps(data), file=f)
