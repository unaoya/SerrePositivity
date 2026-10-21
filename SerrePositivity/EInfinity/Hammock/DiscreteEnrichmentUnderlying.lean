module

public import SerrePositivity.EInfinity.Hammock.DiscreteEnrichment

/-!
# 元の離散豊穣圏の射と通常の underlying 圏への比較

概要：元の射を同じ一定単体写像へ送り、豊穣関手を通常の関手へ移す。
方針：元の射の一定単体と元の合成の回収を使う。
規約：元の対象と元の射を保持する。
使われ方：非指定自由圏の普遍性を豊穣関手へ移す。
-/

@[expose] public section
universe u v uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.DiscreteEnrichment
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

def sourceFunctor :
    letI := enrichedCategory (C := C)
    C ⥤ ForgetEnrichment SSet.{v} C := by
  letI := enrichedCategory (C := C)
  exact
    { obj := ForgetEnrichment.of SSet.{v}
      map := fun f => ForgetEnrichment.homOf SSet.{v} (point f)
      map_id := fun X => ForgetEnrichment.homOf_eId SSet.{v} X
      map_comp := fun {X Y Z} f g => by
        have hc := ForgetEnrichment.homOf_comp SSet.{v}
          (C := C) (X := X) (Y := Y) (Z := Z) (point f) (point g)
        exact (congrArg (ForgetEnrichment.homOf SSet.{v}) (point_comp f g)).symm.trans hc }

variable {D : Type uD} [EnrichedCategory SSet.{v} D]

def ordinaryFunctor :
    letI := enrichedCategory (C := C)
    EnrichedFunctor SSet.{v} C D → (C ⥤ ForgetEnrichment SSet.{v} D) := by
  letI := enrichedCategory (C := C)
  intro F
  exact sourceFunctor ⋙ F.forget

end SerrePositivity.EInfinity.Hammock.DiscreteEnrichment
