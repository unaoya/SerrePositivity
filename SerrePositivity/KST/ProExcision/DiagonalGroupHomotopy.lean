module
public import SerrePositivity.KST.ProExcision.DiagonalGroupBar

/-!
# 次数ごとに自然な実群ホモトピーの対角への制限

概要：係数次数ごとに自然な m 次ホモトピーから、単体的群の対角 bar 上の実 m 次比較を構成する。
方針：区間射の次数 k の成分を対角で使い、係数方向と nerve 方向の自然性を合成する。
規約：KST Lemma 4.16 の単体環への移送。H_* の結論や対角比較の存在は仮定しない。
使われ方：離散環上で関手的に構成した実比較を単体環へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial
variable {M N : SimplicialObject GrpCat.{u}} {f g : M ⟶ N} {m : ℕ}

/-- 概要：係数方向に自然な実区間射を対角 bar の線形区間射へ制限する。
方針：係数次数 k と nerve 次数 k で実射を評価し、二方向の自然性で単体性を示す。
規約：KST 4.16、区間射は全次数で定義する。
使われ方：対角の実 m 次ホモトピーの区間射。 -/
def diagonalGroupCylinderMap
    (h : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap (f.app k).hom) (groupLinearizedMap (g.app k).hom) m)
    (hnat : ∀ {k l} (φ : k ⟶ l),
      linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ (M.map φ).hom)) ≫ (h l).h =
        (h k).h ≫ groupLinearizedMap (N.map φ).hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder (simplicialGroupBar M) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (simplicialGroupBar N) where
  app k := (h k).h.app k
  naturality {k l} φ := by
    rw [linearizedGroupBar_cylinder_decomposition, Category.assoc, (h l).h.naturality φ]
    have hn := congrArg (fun t ↦ t.app k) (hnat φ)
    change (linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ (M.map φ).hom))).app k ≫
        (h l).h.app k = (h k).h.app k ≫ (groupLinearizedMap (N.map φ).hom).app k at hn
    rw [← Category.assoc, hn, Category.assoc, ← linearizedGroupBar_map_decomposition]

/-- 概要：係数方向に自然な次数ごとの m 次ホモトピーは対角で実 m 次ホモトピーを与える。
方針：構成した対角の区間射に、次数ごとの両端条件を同じ次数で適用する。
規約：KST Lemma 4.16、零次を含む非被約 C(H)。
使われ方：単体環上の右乗法の実比較を構成する。 -/
def diagonalGroupMHomotopy
    (h : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap (f.app k).hom) (groupLinearizedMap (g.app k).hom) m)
    (hnat : ∀ {k l} (φ : k ⟶ l),
      linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ (M.map φ).hom)) ≫ (h l).h =
        (h k).h ≫ groupLinearizedMap (N.map φ).hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (simplicialGroupBarMap f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (simplicialGroupBarMap g)) m where
  h := diagonalGroupCylinderMap h hnat
  h₀ n hn := (h (op ⦋n⦌)).h₀ n hn
  h₁ n hn := (h (op ⦋n⦌)).h₁ n hn

end SerrePositivity.KST.ProExcision
