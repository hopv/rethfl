# Docker

## Building an Image
Run

``` sh
docker buildx build . -t rethfl -f docker/Dockerfile
```
at the root directory of this repository.
Note that we use `buildx` for multiplatform support.

## Running Rethfl
Just prepend `docker run <image name>` in front of `rethfl`, its options and the input file.
For example,
``` sh
docker run rethfl:latest rethfl input/ok/valid/sum.in --show-refinement
```

## Developing inside a continer

``` sh
docker run -it [--rm] rethfl:latest /bin/bash
```
will let you get into the container.
You will find this repository at `/root/rethfl`.
