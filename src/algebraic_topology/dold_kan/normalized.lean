/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.projectors
import for_mathlib.idempotents.functor_categories
import for_mathlib.idempotents.functor_extension

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.simplicial_object
open category_theory.idempotents
open simplex_category
open opposite
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace dold_kan

universe v

variables {C : Type*} [category.{v} C] [preadditive C]
variables {X : simplicial_object C}

end dold_kan

end algebraic_topology
