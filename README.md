
## REQUIREMENTS

This library compiles with Coq8.4pl6 [1].

For compatibility with Coq version 8.5beta2 [2], use branch [V8.5beta2](https://github.com/rs-/Triangles/tree/V8.5beta2).

A version with universe polymorphism is available in branch [V8.5beta2-w-poly](https://github.com/rs-/Triangles/tree/V8.5beta2-w-poly)



## INSTALLATION

```
$ make all
```

## Standard documentation

produces the HTML documentation as provided by the coqdoc tool

```
$ make html
```

## Enhanced documentation [requires markdown]

produces enhanced HTML documentation with a table of contents in line with the article

requires the markdown tool

```
$ make doc
```

[1] http://coq.inria.fr/distrib/V8.4pl6/

[2] http://coq.inria.fr/distrib/V8.5beta2/
