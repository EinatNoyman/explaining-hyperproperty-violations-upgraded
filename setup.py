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
    extras_require={
        # needed only for `-solver pysat`, a verbatim port of the tool's
        # original backend kept for before/after comparison with cvc5.
        'pysat': ['python-sat', 'satispy'],
    },
    python_requires='>=3.7'
)