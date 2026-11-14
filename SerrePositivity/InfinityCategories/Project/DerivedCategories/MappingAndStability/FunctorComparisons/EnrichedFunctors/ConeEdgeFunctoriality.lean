module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.ComplexEdgeCalculus
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.PullbackComparison

/-! # 錐の指定脚と包含の可換性

概要：錐を後合成しても指定脚の辺は後合成した元の辺である。
方針：Yoneda の自然性で一単体を比較する。
規約：錐の所属証明を変更しても脚は変わらない。使われ方：semifree の比較を全複体へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory SSet DifferentialGraded

open scoped _root_.Simplicial

/-- 概要：錐を単体的写像で後合成する。
方針：錐の写像と固定図式をともに後合成する。
規約：頂点も写像の像へ送る。使われ方：全複体への包含。 -/
def derivedConePostcomp {K X Y : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q) := ⟨c.val ≫ q, by rw [← Category.assoc, c.property]⟩

/-- 概要：後合成した錐の脚は、元の脚の辺の像である。
方針：Yoneda の合成公式と射の結合則を用いる。
規約：一単体そのものの等式。使われ方：脚の鎖写像の比較。 -/
lemma derivedConeLeg_postcomp_edge {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (q : X ⟶ Y) (v : K _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg c v).map ((truncation 2).map q)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (derivedConePostcomp c q) v).edge := by
  change q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm v) ≫ c.val)) =
      SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm v) ≫ (c.val ≫ q))
  simpa only [Category.assoc] using
    (SSet.yonedaEquiv_comp ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm v) ≫ c.val) q).symm

/-- 概要：錐の写像が等しければ、図式の固定条件の表記に関わらず脚の一単体は等しい。
方針：脚の定義に写像の等式を代入する。
規約：図式の等式による rebase も許す。使われ方：標準 fiber 錐への同定。 -/
lemma derivedConeLeg_edge_eq_of_val_eq {K X : SSet.{u}} {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (h : c.val = d.val) (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg c v).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg d v).edge := by
  change SSet.yonedaEquiv (_ ≫ _ ≫ c.val) = SSet.yonedaEquiv (_ ≫ _ ≫ d.val)
  rw [h]

variable {S : Type u} [CommRing S]

/-- 概要：semifree の標準 fiber 錐を全複体へ送ると標準 fiber 錐の写像になる。
方針：標準四角形の包含像の公式を錐の写像へ適用する。
規約：固定図式の等式は別に扱い、ここでは錐の写像を同定する。使われ方：指定脚の比較。 -/
lemma derivedSquareFiberCone_inclusion_val
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    (derivedConePostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)) _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap).val := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion = _
  rw [Category.assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare _ _ _ _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare_inclusion]
  rfl

/-- 概要：semifree の標準 fiber 錐の第一脚を包含すると第一射影の arrow になる。
方針：後合成の脚の式、標準錐の写像の一致、標準下辺の式を続けて用いる。
規約：両端の複体の同定も含む。使われ方：比較射と第一射影の合成。 -/
lemma derivedSquareFiberCone_bottom_arrow
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F))
      (SSet.yonedaEquiv (stdSimplex.δ 1 ≫ horn₂₂.ι₀₂))).map
        ((truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_arrow_eq_complexEdge
  exact (derivedConeLeg_postcomp_edge _ _ _).trans
    ((derivedConeLeg_edge_eq_of_val_eq _ _ (derivedSquareFiberCone_inclusion_val F) _).trans
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_pullback_bottom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare _ _)).trans
        ((congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_standardFiberSquare_bottom _ _)).trans
          (SSet.yonedaEquiv.apply_symm_apply _))))

/-- 概要：semifree の標準 fiber 錐の第二脚を包含すると第二射影の arrow になる。
方針：後合成と標準左辺の公式で両端付きの射を同定する。
規約：両端の複体の同定も含む。使われ方：比較射と第二射影の合成。 -/
lemma derivedSquareFiberCone_left_arrow
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F))
      (SSet.yonedaEquiv (stdSimplex.δ 1 ≫ horn₂₂.ι₁₂))).map
        ((truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_arrow_eq_complexEdge
  exact (derivedConeLeg_postcomp_edge _ _ _).trans
    ((derivedConeLeg_edge_eq_of_val_eq _ _ (derivedSquareFiberCone_inclusion_val F) _).trans
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_pullback_left (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare _ _)).trans
        ((congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_standardFiberSquare_left _ _)).trans
          (SSet.yonedaEquiv.apply_symm_apply _))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
