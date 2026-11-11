module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
public import SerrePositivity.Spectra.PointedSimplicialSet.Spheres

/-!
概要：境界を潰した球面からの点つき射と境界定数単体の同値。
方針：球面の実際の cofiber の普遍性を PtSimplex の相対条件へ移す。
規約：標的の Kan 性は不要。球面の次元は零も許す。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。円の乗法射と有理化の実構成。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SphereSimplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：球面からの点つき射を境界定数単体へ引き戻す。
方針：標準単体から商への射を前合成し、基点条件を頂点の定数射で表す。
規約：実際の単体の射を保持する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面の射のホモトピー類の代表。 -/
def toSimplex (X : PointedSimplicialSet.{u}) (n : ℕ)
    (f : PointedSimplicialSet.sphere.{u} n ⟶ X) : X.right.PtSimplex n X.basepoint where
  map := PointedObject.cofiberQuotient (boundary.{u} n).ι ≫ f.right
  comm := by
    have hf : (PointedObject.cofiber (boundary.{u} n).ι).hom ≫ f.right = X.hom := Under.w f
    rw [← Category.assoc, PointedObject.cofiberQuotient_condition, Category.assoc, hf,
      Subcomplex.ofSimplex_ι, SSet.comp_const]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const X _

/-- 概要：境界定数単体を球面からの点つき射へ降ろす。
方針：境界の定数条件を cofiber の降下条件へ移す。
規約：標的の基点は PtSimplex の指定基点そのもの。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。指定した群の類を球面の射として実現する。 -/
def toMap (X : PointedSimplicialSet.{u}) (n : ℕ) (s : X.right.PtSimplex n X.basepoint) :
    PointedSimplicialSet.sphere.{u} n ⟶ X :=
  PointedObject.cofiberDesc (boundary.{u} n).ι X s.map (by
    rw [s.comm, Subcomplex.ofSimplex_ι, SSet.comp_const]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const X _).symm)

/-- 概要：球面の点つき射と境界定数単体の標準同値。
方針：cofiber の引き戻しと降下が互いに逆であることを使う。
規約：任意の自然数次元。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面を源とする π_* の代表計算。 -/
def equiv (X : PointedSimplicialSet.{u}) (n : ℕ) :
    (PointedSimplicialSet.sphere.{u} n ⟶ X) ≃ X.right.PtSimplex n X.basepoint where
  toFun := toSimplex X n
  invFun := toMap X n
  left_inv f := by
    apply PointedObject.cofiber_hom_ext (boundary.{u} n).ι
    exact PointedObject.cofiberQuotient_desc (boundary.{u} n).ι X _ _
  right_inv s := by
    apply RelativeMorphism.ext
    exact PointedObject.cofiberQuotient_desc (boundary.{u} n).ι X _ _

/-- 概要：球面からの射の後合成は境界定数単体の後合成に一致。
方針：商への射と後合成の結合則を使う。
規約：基点保存の証明は点つき射から取る。
使われ方：Goerss–Jardine I §7。円の乗法射の基本類での計算。 -/
theorem equiv_comp {X Y : PointedSimplicialSet.{u}} (n : ℕ)
    (s : PointedSimplicialSet.sphere.{u} n ⟶ X) (f : X ⟶ Y) :
    equiv Y n (s ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex f.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f) (equiv X n s) := by
  apply RelativeMorphism.ext
  rfl

end

end SerrePositivity.KST.Spectra.SphereSimplex
