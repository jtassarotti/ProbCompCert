from numpy import *


alpha = random.normal(0, 1)
beta = random.normal(0, 1)
sigma = max(0.0, random.normal(1, .1))

print(alpha)
print(beta)
print(sigma)


x = [12.4, 29.4, 10.1, 0.2, 0.6,  9.9,  9.9,  9.9,  9.9, 8.8]
y = []
for i in range(len(x)):
    y.append(round(random.normal(alpha + beta * x[i], sigma), 5))


print(y)
