from setuptools import setup, find_packages

setup(
    name='explainhyper',
    version='0.1.0',
    packages=find_packages(),
    install_requires=[
        'py-aiger',
        'graphviz',
        'pygraphviz',
        'numpy',
        'cvc5'
    ],
    python_requires='>=3.7'
)