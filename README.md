# pointfree-hse

The [original pointfree](https://github.com/bmillwood/pointfree) says at the
bottom of its readme:

> It would be nice to make pointfree a library that operated on ASTs.

This library goes some way to addressing that remark. It can also eliminate
points one-by-one, which should be a (minor) legibility improvement. (This
version shares no code with the original, since I thought it would be fun to
work out how to do it independently.)

While the original pointfree was very much "eliminate points and then apply a
variety of refactoring transformations to improve the result", this one is so
far very focused on eliminating points. The refactoring capability is also an
interesting tool, but probably best as a separate step.
