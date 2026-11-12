module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberConnecting
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FixedHomotopyComponent

/-! # Cofiber と suspension の比較の最初の二成分

概要：比較の第一成分は始点の恒等射であり、第二成分は零射である。
方針：始点固定条件を自然変換の恒等成分へ移し、第二成分の標的の零対象性を使う。
規約：第一成分の端点輸送は Arrow の等号に含める。
使われ方：S4 の接続射の選択の比較と自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：cofiber と指定 suspension の比較の第一成分は元の始点の恒等射。
方針：比較ホモトピーの始点固定条件を固定頂点の自然変換の成分の式へ移す。
規約：異なる端点表示を Arrow の等号で同定する。
使われ方：接続射の比較が始点で恒等であることの証明。 -/
lemma cofiberSuspensionShortComplexMap_τ₁_arrow {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionShortComplexMap t ht s).τ₁ =
      Arrow.mk (𝟙 t.hoShortComplex.X₁) := by
  let Q := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSuspensionComparison t.square ht s
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTransOfEndpoints_fixedVertex_arrow Q.h Q.h₀ Q.h₁
    (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSuspensionComparison_source t.square ht s)
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  exact h

/-- 概要：比較の第一成分は始点の等号による輸送そのものである。
方針：恒等射との Arrow の等式を射の等式に展開し、同じ始点の輸送を消す。
規約：suspension の source_eq の逆向きの輸送。
使われ方：cofiber 比較の可換式を始点の同じ図式へ戻す。 -/
lemma cofiberSuspensionShortComplexMap_τ₁_eqToHom {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionShortComplexMap t ht s).τ₁ =
      eqToHom (show t.hoShortComplex.X₁ = s.toZeroTriangle.hoShortComplex.X₁ from
        congrArg SSet.HomotopyCategory.mk s.source_eq.symm) := by
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (cofiberSuspensionShortComplexMap_τ₁_arrow t ht s)
  simpa only [eqToHom_refl, Category.id_comp] using hf

/-- 概要：cofiber と suspension の比較の第一成分は同型。
方針：Arrow 表示の恒等射との等式で同型性を移す。
規約：端点の等号による輸送を許す。使われ方：三角形の比較の第一対象。 -/
lemma cofiberSuspensionShortComplexMap_τ₁_isIso {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionShortComplexMap t ht s).τ₁ := by
  have h := congrArg (fun a : Arrow (hoFunctor.obj X) ↦ IsIso a.hom)
    (cofiberSuspensionShortComplexMap_τ₁_arrow t ht s)
  apply h.mpr
  change IsIso (𝟙 t.hoShortComplex.X₁)
  infer_instance

/-- 概要：cofiber と suspension の比較の第二成分は零射。
方針：suspension の右下の零対象への射の一意性を使う。
規約：任意の零射構造。使われ方：比較図式の中央成分。 -/
lemma cofiberSuspensionShortComplexMap_τ₂_eq_zero {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionShortComplexMap t ht s).τ₂ = 0 :=
  s.other_zero.isZeroHo.eq_zero_of_tgt (C := hoFunctor.obj X) _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
