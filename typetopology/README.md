# The TypeTopology-based Agda development

These modules use Martín Escardó and collaborators’ TypeTopology at commit
`52ed2eb58d72a6bab0dd70480fa73e2291b08219`. The project licenses its original Agda modules under the GNU General Public
License, version 3 only (`GPL-3.0-only`). The combined development is
distributed under the same license. The notices for incorporated third-party material and its authors
are listed in the [source credits](../docs/sources.md). [Full GPLv3 text](../apartness/notices/TypeTopology-LICENSE.txt)

| Entry point | What it checks |
| --- | --- |
| [Cohesion](source/gist/Cohesion/index.lagda) | All three safe indexes together. |
| [RealCohesion](source/gist/RealCohesion/index.lagda) | Real cohesion, the intermediate value and fixed-point theorems, and internal obstructions. |
| [Orbifolds](source/gist/Orbifolds/index.lagda) | The orbifold theorem for ordinary étale groupoids and the comparison using spectra of Weil algebras. |
| [CohesiveApartness](source/gist/CohesiveApartness/index.lagda) | The two apartness questions. The historically separate seven-module release is also available as a [patch](cohesive-apartness.patch). |

## Build

Run these commands from the root of this repository with Agda 2.9.0 and a UTF-8 locale.

```sh
git clone https://github.com/martinescardo/TypeTopology.git tt
git -C tt checkout 52ed2eb58d72a6bab0dd70480fa73e2291b08219
cp -R typetopology/source/gist/. tt/source/gist/
cd tt
agda source/gist/Cohesion/index.lagda
agda source/gist/CohesiveApartness/FlatSplit.lagda
agda source/gist/RealCohesion/FlatSplit.lagda
```

The first command to Agda checks the native sharp development under
`--safe --without-K --cohesion`. The two `FlatSplit` entry points use
crisp pattern matching and are checked separately. They also support
Agda 2.8.0. Use a fresh TypeTopology tree at the same revision when
switching compiler versions.
