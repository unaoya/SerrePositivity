module

public import SerrePositivity.KST.Spectra.GroupCochainHomotopyDiagram

/-!
概要：自由軌道の射の前合成が正次数ホモトピー群の各関数座標へ誘導する作用の式。
方針：評価との可換式を代表単体と写像の合成に適用する。
規約：基点は各座標で係数の標準基点。
使われ方：Goerss–Jardine I §7、VIII §2。余単体群の顔・退化の係数への作用。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自由軌道の前合成は π_* の関数座標で添字の変更と係数の群作用になる。
方針：関数の前合成と評価の式を境界定数単体上で使う。
規約：k は実際の次数 k+1。添字集合は任意。
使われ方：Goerss–Jardine VIII §2。群 cochain の π_* の余単体構造の座標式。 -/
lemma pointedFunctionPre_homotopy_coordinate {G S T : Type u} [Group G]
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S))
    (B : Action PointedSimplicialSet.{u} G) [KanComplex B.V.right] (k : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (SimplicialFunctionComplex.pointedObj S B.V).right k
      (SimplicialFunctionComplex.pointedObj S B.V).basepoint) (t : T) :
    SimplicialFunctionComplex.pointedHomotopyEquiv T B.V k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (pointedFunctionPre θ B).right
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) a) t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (B.ρ (θ.hom ((1 : G), t)).1).asHom.right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
        (SimplicialFunctionComplex.pointedHomotopyEquiv S B.V k a (θ.hom ((1 : G), t)).2) := by
  induction a using Quotient.inductionOn with | h r => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval T B.V.right t) rfl
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (pointedFunctionPre θ B).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) r)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (B.ρ (θ.hom ((1 : G), t)).1).asHom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S B.V.right (θ.hom ((1 : G), t)).2) rfl r))
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
  apply RelativeMorphism.ext
  have he : (pointedFunctionPre θ B).right ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval T B.V.right t =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S B.V.right (θ.hom ((1 : G), t)).2 ≫
        (B.ρ (θ.hom ((1 : G), t)).1).asHom.right :=
    functionPre_eval θ ((PointedSimplicialSet.forget.mapAction G).obj B) t
  change (r.map ≫ (pointedFunctionPre θ B).right) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval T B.V.right t =
    (r.map ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S B.V.right (θ.hom ((1 : G), t)).2) ≫
      (B.ρ (θ.hom ((1 : G), t)).1).asHom.right
  rw [Category.assoc, he, ← Category.assoc]

end

end SerrePositivity.KST.Spectra.FreeActionFamily
