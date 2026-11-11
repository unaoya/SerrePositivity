module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ResolutionPathPrefix

/-!
# coherent pinched 単体の先頭面の Hom は単位である

概要：先頭面に含まれる任意の Path の像は、端点を同定すると dg 単位の定数単体となる。
方針：pinched 条件の豊穣関手の等式から Hom の等式を回収する。
規約：全ての単体次数で述べ、頂点の等式だけに弱めない。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の解像の引き戻しで除かれる先頭部分の消去。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded CartesianMonoidalCategory
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

private lemma coherentFunctor_map_eq {n : ℕ}
    (F G : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌) (h : F = G)
    (i j : SimplicialThickening (ULift.{u} (Fin (n + 1)))) :
    F.map i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (congrArg (fun T ↦ T.obj i) h) (congrArg (fun T ↦ T.obj j) h)) = G.map i j := by
  subst G
  simp only [eqToHom_refl, Category.comp_id]

/-- 概要：coherent pinched 単体の先頭面の Hom 写像は端点の移送後に単位に定値となる。
方針：先頭面の等式を標準の F1 の頂点に移して Hom の等式を取り出す。
規約：始点・終点の番号は先頭面内の任意の二点。
使われ方：Kerodon 2.5.9（Tag 00SC） の先頭部分と後半部分への分解後の単位則。 -/
lemma coherentPinched_front_hom {x y : ClosedCategory R D} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) (i j : Fin (n + 1)) :
    nerveMap (SimplicialThickening.functorMap Fin.castSuccOrderEmb.toOrderHom.uliftMap
      (.mk (ULift.up i)) (.mk (ULift.up j))) ≫
      s.val.map (.mk (ULift.up i.castSucc)) (.mk (ULift.up j.castSucc)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s j)) =
      toUnit _ ≫ eId SSet x := by
  have hsrc : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op s.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) n :=
    s.source.trans (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentNerveVertex_eq_vertex x).symm)
  have h := coherentFunctor_map_eq _ _ hsrc (.mk (ULift.up i)) (.mk (ULift.up j))
  have h' := h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveConstant_map x n (.mk (ULift.up i)) (.mk (ULift.up j)))
  change (nerveMap
    (SimplicialThickening.functorMap Fin.castSuccOrderEmb.toOrderHom.uliftMap
      (.mk (ULift.up i)) (.mk (ULift.up j))) ≫
        s.val.map (.mk (ULift.up i.castSucc)) (.mk (ULift.up j.castSucc))) ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s j)) =
      toUnit _ ≫ eId SSet x at h'
  simpa only [Category.assoc] using h'

/-- 概要：先頭面内の任意の Path の単体の像は標準 Hom の単位単体である。
方針：先頭面の Hom 写像の等式をその単体で評価する。
規約：順序条件は入力の Path 自身が持つ。
使われ方：HA 1.3.1.17 の解像の引き戻しの評価の前半の消去。 -/
lemma coherentPinched_front_value {x y : ClosedCategory R D} {n d : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) (i j : Fin (n + 1))
    (P : (nerve (SimplicialThickening.Path (ULift.up i : ULift.{u} (Fin (n + 1)))
      (ULift.up j))) _⦋d⦌) :
    (s.val.map (.mk (ULift.up i.castSucc)) (.mk (ULift.up j.castSucc)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s j))).app (Opposite.op ⦋d⦌)
      ((nerveMap (SimplicialThickening.functorMap Fin.castSuccOrderEmb.toOrderHom.uliftMap
        (.mk (ULift.up i)) (.mk (ULift.up j)))).app _ P) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) (D := D) x d := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (coherentPinched_front_hom s i j) (Opposite.op ⦋d⦌)) P

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
