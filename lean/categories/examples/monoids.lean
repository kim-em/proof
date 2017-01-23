-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..functor
import ..natural_transformation
import ..products
import ..monoidal_category

namespace tqft.categories.examples.monoids

open tqft.categories

instance CategoryOfMonoids : Category := 
{
    Obj := Π α : Type, monoid α,
    Hom := sorry,

    identity := sorry,
    compose  := sorry,

    left_identity  := sorry,
    right_identity := sorry,
    associativity  := sorry
}

end tqft.categories.examples.monoids
