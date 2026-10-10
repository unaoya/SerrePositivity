module

public import SerrePositivity.CategoryTheory.LocalizationTStructure

/-!
# 分母の切り詰め条件からの Verdier 商の t 構造

三角部分圏 `P` に対する標準的な Verdier 局所化 `P.trW.Localization` に、
`LocalizationTStructure` の構成を適用する。
有界な場合には商自体が冪等完備となり、冪等完備化の全対象が商の対象で表せる。

仮定 `hτ` は非正切り詰めが `P.trW` を保つという具体的な射の条件である。
切り詰め安定性と heart の Serre 条件からこの仮定を供給する証明は別途必要である。
-/

@[expose] public section

universe v u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Idempotents

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (t : TStructure C) (P : ObjectProperty C) [P.IsTriangulated]
  (hτ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P.trW f → P.trW ((t.truncLE 0).map f))

include hτ in
omit [IsTriangulated C] [P.IsTriangulated] in
/-- 非正切り詰めが分母を保つならば、切り詰めた分母は Verdier 商で可逆になる。 -/
lemma verdier_truncLE_inverts : P.trW.IsInvertedBy (t.truncLE 0 ⋙ P.trW.Q) :=
  fun _ _ f hf ↦ Localization.inverts P.trW.Q P.trW _ (hτ f hf)

/-- 分母の切り詰め条件を満たす Verdier 商上の t 構造。 -/
noncomputable def verdierTStructure : TStructure P.trW.Localization :=
  localizationTStructure t P.trW.Q P.trW (verdier_truncLE_inverts t P hτ)

/-- Verdier 商の非正側は、元の非正側の本質像である。 -/
lemma verdierTStructure_le (n : ℤ) :
    (verdierTStructure t P hτ).le n = (t.le n).map P.trW.Q := rfl

/-- Verdier 商の非負側は、元の非負側の本質像である。 -/
lemma verdierTStructure_ge (n : ℤ) :
    (verdierTStructure t P hτ).ge n = (t.ge n).map P.trW.Q := rfl

/-- 標準的な Verdier 商関手は構成した t 構造に関して t 完全である。 -/
lemma verdierTStructure_tExact : P.trW.Q.TExact t (verdierTStructure t P hτ) :=
  localizationTStructure_tExact t P.trW.Q P.trW (verdier_truncLE_inverts t P hτ)

/-- 元の t 構造が有界ならば、Verdier 商上の t 構造も有界である。 -/
lemma verdierTStructure_bounded (hb : ∀ X : C, t.bounded X) (Y : P.trW.Localization) :
    (verdierTStructure t P hτ).bounded Y :=
  localizationTStructure_bounded t P.trW.Q P.trW (verdier_truncLE_inverts t P hτ) hb Y

include hτ in
/-- 有界性と分母の切り詰め条件を満たす Verdier 商は冪等完備である。 -/
lemma verdier_isIdempotentComplete (hb : ∀ X : C, t.bounded X) :
    IsIdempotentComplete P.trW.Localization :=
  localization_isIdempotentComplete t P.trW.Q P.trW (verdier_truncLE_inverts t P hτ) hb

/-- 条件を満たす有界 Verdier 商と、その冪等完備化の同値。 -/
noncomputable def verdierKaroubiEquivalence (hb : ∀ X : C, t.bounded X) :
    P.trW.Localization ≌ Karoubi P.trW.Localization := by
  have := verdier_isIdempotentComplete t P hτ hb
  exact toKaroubiEquivalence P.trW.Localization

include hτ in
/-- 冪等完備化した商の任意の対象は、元の圏の実際の対象の像に同型である。 -/
lemma verdierKaroubi_has_representative (hb : ∀ X : C, t.bounded X)
    (Y : Karoubi P.trW.Localization) :
    ∃ X : C, Nonempty ((toKaroubi P.trW.Localization).obj (P.trW.Q.obj X) ≅ Y) := by
  have := verdier_isIdempotentComplete t P hτ hb
  obtain ⟨Z, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (toKaroubi P.trW.Localization) Y
  have := Localization.essSurj P.trW.Q P.trW
  exact ⟨P.trW.Q.objPreimage Z,
    ⟨(toKaroubi P.trW.Localization).mapIso (P.trW.Q.objObjPreimageIso Z) ≪≫ e⟩⟩

end SerrePositivity
