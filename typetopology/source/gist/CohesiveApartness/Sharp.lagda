Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.CohesiveApartness.index.

This module is licensed under the GNU General Public License, version 3.
SPDX-License-Identifier: GPL-3.0-only

The sharp modality ♯, natively.

Agda 2.9.0 adds the modality @♯ to --cohesion, as the right adjoint of
@♭, and allows it on the fields of records [1]. The type ♯ A is then
a record with one field of modality ♯, as in the Agda documentation
[1]. It obeys Shulman's rules for ♯ [2, §3]:

 * in the type ♯ A, every variable occurring in A counts as crisp;

 * an element of ♯ A is defined by copattern matching, after which
   every variable in the context counts as crisp;

 * the field can be projected from a crisp element of ♯ A.

From these rules we derive the unit of ♯, recursion into types of
the form ♯ B, crisp induction (to construct an element of ♯ (C x) for
an arbitrary x of a crisp type, it suffices to construct C x for
crisp x), and elimination on crisp elements. Everything here is
--safe.

Agda 2.8 has no ♯, and so gist.CohesiveApartness.FlatSplit proves the
consequence of crisp induction that this folder needs, that 𝟚 is
♭-discrete, with --flat-split instead.
gist.CohesiveApartness.CrispInduction derives it from the ♯ of this
module, in --safe mode.

The field is called ε♯ rather than ε, so that opening this module
does not take the name ε, which TypeTopology uses for other
purposes.

[1] The Agda documentation, Language, Flat Modality, for Agda 2.9.0.
    https://agda.readthedocs.io/en/latest/language/flat.html

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.CohesiveApartness.Sharp where

open import MLTT.Spartan

record ♯ {𝓤 : Universe} (@♯ A : 𝓤 ̇ ) : 𝓤 ̇ where
 constructor sharp
 field
  @♯ ε♯ : A

open ♯ public

\end{code}

The unit, elimination on crisp elements, recursion, crisp induction
and the action on maps.

\begin{code}

unit-sharp : {𝓤 : Universe} {A : 𝓤 ̇ } → A → ♯ A
unit-sharp a .ε♯ = a

crisp-elim-sharp : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } (@♭ w : ♯ A) → A
crisp-elim-sharp w = w .ε♯

rec-sharp : {𝓤 𝓥 : Universe} {A : 𝓤 ̇ } {B : 𝓥 ̇ }
          → (A → ♯ B) → ♯ A → ♯ B
rec-sharp f a .ε♯ = f (a .ε♯) .ε♯

crisp-ind-sharp : {@♭ 𝓤 : Universe} {𝓥 : Universe} {@♭ A : 𝓤 ̇ }
                  (C : A → 𝓥 ̇ )
                → ((@♭ x : A) → C x)
                → (x : A) → ♯ (C x)
crisp-ind-sharp C f x .ε♯ = f x

♯-map : {𝓤 𝓥 : Universe} {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ♯ A → ♯ B
♯-map f a .ε♯ = f (a .ε♯)

\end{code}

The sharp record follows the example in the Agda manual.
The following notice accompanies that example.

Copyright (c) 2005-2026 remains with the authors.
Agda 2 was originally written by Ulf Norell,
partially based on code from Agda 1 by Catarina Coquand and Makoto Takeyama,
and from Agdalight by Ulf Norell and Andreas Abel.
Cubical Agda was originally contributed by Andrea Vezzosi.

Agda 2 is currently actively developed mainly by Andreas Abel,
Nathaniel Burke, Lawrence Chonavel, Jesper Cockx,
Nils Anders Danielsson, and András Kovács.

Further, Agda 2 has received contributions by, amongst others,
Arthur Adjedj, Guillaume Allais, Malin Altenmüller, Stevan Andjelkovic,
Marcin Benke, Jean-Philippe Bernardy, Guillaume Brunerie,
James Chapman, Liang-Ting Chen, Joris Ceulemans, Jonathan Coates,
Matthew Daggitt, Dominique Devriese, Marko Dimjašević, Péter Diviánszky,
Lucas Escot, Robert Estelle,
Naïm Camille Favier, Kuen-Bang Hou (Favonia), Olle Fredriksson,
Paolo G. Giarrusso, Adam Gundry, Daniel Gustafsson,
Philipp Hausmann, Alex Haršáni,
Patrik Jansson, Alan Jeffrey, Phil de Joux,
Wolfram Kahl, Philip Kaludercic, Andre Knispel, Wen Kokke,
John Leo, Amélia Liao, Ziyang Liu, Fredrik Lindblad, Víctor López Juan, Ting-Gan Lua,
Francesco Mazzoli, Stefan Monnier, Guilhem Moulin, Reed Mullanix,
Konstantin Nisht, Fredrik Nordvall Forsberg, Ulf Norell, Andreas Nuyts,
Herminie Pagel, Josselin Poiret, Nicolas Pouillard, Jonathan Prieto,
Christian Sattler, Artem Shinkarov, Michael Shulman, Andrés Sicard-Ramírez, Nate Soares,
Makoto Takeyama, Andrea Vezzosi, Szumi Xie, Nobuo Yamashita,
Noam Zeilberger, and Tesla Ice Zhang.
The full list of contributors is available at
https://github.com/agda/agda/graphs/contributors or from the git
repository via ``git shortlog -sne``.

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
