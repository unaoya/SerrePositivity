module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornSubdivisionFaceMaps
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionCommonFace

/-!
# horn の実際の細分と面の nerve の同型

概要：正次元 horn の細分比較は同型である。
方針：二つの余面表示を共通の小さい面から比較して単射性を示し、既証の全射性と合わせる。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の細分された horn の模型の同定。
使われ方：面の nerve の包含の anodyne 性を、実際の細分された horn へ移す。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits
open scoped _root_.Simplicial

/--
概要：正次元 horn の細分比較は各次数で単射である。
方針：各元を余面の像で表し、像が一致する二つの余面を共通の面へ持ち上げる。
規約：一次元では許された余面が一つだけなので、同じ余面の単射性に帰着する。
使われ方：細分比較の同型性。
-/
theorem hornSubdivisionComparison_app_injective (n : ℕ) (k : Fin (n + 2))
    (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((hornSubdivisionComparison.{u} (n + 1) k).app d) := by
  intro a b hab
  obtain ⟨j, hj, t, ht⟩ := hornSubdivisionNerveFaceCover n k d a
  obtain ⟨l, hl, u, hu⟩ := hornSubdivisionNerveFaceCover n k d b
  have h : (SimplexCategory.sd.{u}.map (SimplexCategory.δ j)).app d t =
      (SimplexCategory.sd.{u}.map (SimplexCategory.δ l)).app d u := by
    have h' : ((hornSubdivisionFaceMap n k j hj ≫ hornSubdivisionComparison (n + 1) k ≫
        nerveMap (hornFaceInclusion (n + 1) k).monotone.functor).app d) t =
      ((hornSubdivisionFaceMap n k l hl ≫ hornSubdivisionComparison (n + 1) k ≫
        nerveMap (hornFaceInclusion (n + 1) k).monotone.functor).app d) u := by
      change (nerveMap (hornFaceInclusion (n + 1) k).monotone.functor).app d
          ((hornSubdivisionComparison (n + 1) k).app d
            ((hornSubdivisionFaceMap n k j hj).app d t)) =
        (nerveMap (hornFaceInclusion (n + 1) k).monotone.functor).app d
          ((hornSubdivisionComparison (n + 1) k).app d ((hornSubdivisionFaceMap n k l hl).app d u))
      rw [ht, hu, hab]
    rw [hornSubdivisionFaceMap_ambient, hornSubdivisionFaceMap_ambient] at h'
    exact h'
  by_cases hjl : j = l
  · subst l
    have htu := subdivisionFace_app_injective j d h
    rw [← ht, ← hu, htu]
  · cases n with
    | zero =>
      exfalso
      have h₁ : j.val ≠ k.val := fun heq => hj (Fin.ext heq)
      have h₂ : l.val ≠ k.val := fun heq => hl (Fin.ext heq)
      have h₃ : j.val ≠ l.val := fun heq => hjl (Fin.ext heq)
      omega
    | succ n =>
      obtain ⟨α, β, v, hαβ, hv₀, hv₁⟩ := subdivisionCommonFace n j l hjl d t u h
      calc
        a = (hornSubdivisionFaceMap (n + 1) k j hj).app d t := ht.symm
        _ = (hornSubdivisionFaceMap (n + 1) k j hj).app d
            ((SimplexCategory.sd.map α).app d v) := congrArg _ hv₀.symm
        _ = (hornSubdivisionFaceMap (n + 1) k l hl).app d
            ((SimplexCategory.sd.map β).app d v) :=
          ConcreteCategory.congr_hom
            (congr_app (hornSubdivisionFaceMap_common k j l hj hl α β hαβ) d) v
        _ = b := by rw [hv₁]; exact hu

/--
概要：正次元 horn の細分比較は同型である。
方針：各次数で証明した単射性と全射性を合わせ、前層の同型性へ移す。
規約：零次元の空の horn はここでは扱わない。
使われ方：細分された horn の包含の anodyne 性。
-/
instance hornSubdivisionComparison_isIso (n : ℕ) (k : Fin (n + 2)) :
    IsIso (hornSubdivisionComparison.{u} (n + 1) k) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro d
  exact (isIso_iff_bijective _).mpr
    ⟨hornSubdivisionComparison_app_injective n k d,
      hornSubdivisionComparison_app_surjective n k d⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
