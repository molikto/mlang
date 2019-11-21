# Changelog

the status and the goal of this project is in constant flux now. so before it is minimally-useable to anyone other than the maintainers, only a status report will be here, not all the small changes.

2019-11-21 status: we have lift operator and cumulative universe now.

2019-11-09 status: we ported the project to Dotty, so toolchain is a little bit a mess. we got new HOAS compiler by emitting JVM bytecode, so typechecking is much faster now. we implemented `VHcompU` and other things to make it more similar to cubicaltt, and this also makes `problem` computes much faster, currently it is 200ms on my machine compared to cubicaltt's 40ms, Cubical Agda cannot compute this now (at least last time I checked)

2019-10-30 status: we have implemented a cubical type theory with a core similar to cubicaltt, but with some elaboration to make it easier to use.
we implemented Brunerie's number, but sadly it is not computing (just like all other ctt implementations).
in the past the focus is to get it running to experiment with computation, so there are a fair share of bugs and dark corners.
