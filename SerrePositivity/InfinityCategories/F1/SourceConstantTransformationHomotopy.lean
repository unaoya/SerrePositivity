module

public import SerrePositivity.InfinityCategories.F1.SourceConstantTransformationNaturality

/-!
概要：両端固定の円柱のホモトピーを、定値始域からの変換空間のホモトピーへ戻す。
方針：追加の時間をパラメータへ移し、全時刻の円柱を同時に curry する。
規約：元の図式と指定頂点を時間全体で固定する。
使われ方：錐空間の標準比較のホモトピー右逆。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 概要：元の図式と定値始点を保つ円柱の変形を変換空間のホモトピーにする。
方針：時間を右パラメータへ結合し、二端を固定して curry する。
規約：全円柱を入力として保持。使われ方：fat join の比較のホモトピーの移送。 -/
def sourceConstantTransformationHomotopyOfPrisms
    (a b : T ⟶ intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f))
    (H : SSet.Homotopy (sourceConstantTransformationPrism a) (sourceConstantTransformationPrism b))
    (h₀ : ((SSet.ι₀ (X := K) ▷ T) ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const z)
    (h₁ : ((SSet.ι₁ (X := K) ▷ T) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (K ⊗ T) Δ[1] ≫ fst K T ≫ f) :
    SSet.Homotopy a b := by
  let R := (α_ (K ⊗ (Δ[1] : SSet.{u})) T Δ[1]).inv ≫ H.h
  have hR₀ : (SSet.ι₀ ▷ (T ⊗ (Δ[1] : SSet.{u}))) ≫ R = SSet.const z := by
    change ((α_ K T (Δ[1] : SSet.{u})).inv ≫ ((SSet.ι₀ ▷ T) ▷ Δ[1])) ≫ H.h = _
    rw [Category.assoc, h₀, SSet.comp_const]
  have hR₁ : (SSet.ι₁ ▷ (T ⊗ (Δ[1] : SSet.{u}))) ≫ R = fst K (T ⊗ Δ[1]) ≫ f := by
    change ((α_ K T (Δ[1] : SSet.{u})).inv ≫ ((SSet.ι₁ ▷ T) ▷ Δ[1])) ≫ H.h = _
    rw [Category.assoc, h₁]
    rfl
  let G := sourceConstantTransformationCurry R hR₀ hR₁
  refine ⟨G, ?_, ?_, ?_⟩
  · change SSet.ι₀ ≫ G = a
    apply sourceConstantTransformationPrism_injective
    rw [sourceConstantTransformationPrism_precomp, sourceConstantTransformationPrism_curry]
    change SSet.ι₀ ≫ H.h = sourceConstantTransformationPrism a
    exact H.h₀
  · change SSet.ι₁ ≫ G = b
    apply sourceConstantTransformationPrism_injective
    rw [sourceConstantTransformationPrism_precomp, sourceConstantTransformationPrism_curry]
    change SSet.ι₁ ≫ H.h = sourceConstantTransformationPrism b
    exact H.h₁
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories
