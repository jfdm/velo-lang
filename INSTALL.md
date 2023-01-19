# Building, Installing, and Playing

## Building

To build and use Velo you must first install [Idris 2](https://github.com/idris-lang/Idris2)

Once Idris2 has been installed you can build the project with:

```bash
make velo
```

## Testing

The test suite can be ran using:

```bash
make velo-test-run
```

## Installing

We have yet to add installation scripts or turn this into a serious tool to play with.
This might come later.

That being said, you can copy the binary from `build/exec` to a well known location under `PATH` and you should be able to use it from there.

## Playing

Velo is a very simple language with a simple UX.
We do not provide anything fancy as our interest at the moment is in the tool itself and not necessarily its use by others.

There are examples in the directory called `tests`.
