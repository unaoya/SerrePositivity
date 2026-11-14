module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleSplitConeHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareHomotopyPostcompose
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeSquareData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConePushout
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareTopMiddleIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareVertices
/-!
概要：閉分裂する右 dg 加群の同じ零二胞体四角形の cofiber 性を判定する。
方針：標準 cone から同じ右射影へ降下し、全 dg 自然な収縮で余極限性を移送する。
規約：指定された四辺・対角・上下の次数 −1 成分を厳密に保持する。
使われ方：K-B の native 分裂四角形を全右 dg 加群内で検証する最小入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Category Limits DifferentialGraded
open HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N P Z : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

lemma dgModuleSplitConeDesc_inl (a : M ⟶ N) (p : N ⟶ P) (hap : a ≫ p = 0) :
    _root_.SerrePositivity.DifferentialGraded.compose A (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D a))
      (z := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) P)
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.DifferentialGraded.moduleConeDesc A D a p hap))).val (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D a)
      (add_zero (-1)) = 0 := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext A D
  intro x
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π, _root_.SerrePositivity.DifferentialGraded.moduleConeInlElement_π, ← _root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain,
    _root_.SerrePositivity.DifferentialGraded.moduleConeDesc_eval, _root_.SerrePositivity.DifferentialGraded.complexConeDesc_ofHom, map_zero]
  simp

/-- 概要：元の分裂四角形は全右 dg 加群の実 cofiber 四角形。
方針：同じ標準 cone の実二胞体を後合成し、指定係数との厳密一致で輸送する。
規約：零角は native 零頂点で指定し、全 dg 自然な分裂射を使う。
使われ方：K-B の点ごとの分裂 cofiber 性から Perf へ反映する入口。 -/
lemma dgModuleSplitSquare_isPushout_of_zeroVertex_eq
    (a : M ⟶ N) (r : N ⟶ M) (b : P ⟶ N) (p : N ⟶ P)
    (har : a ≫ r = 𝟙 M) (hbp : b ≫ p = 𝟙 P) (hap : a ≫ p = 0)
    (_hbr : b ≫ r = 0) (hs : r ≫ a + p ≫ b = 𝟙 N)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D M N Z P)
    (hZ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) Z) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex A D)
    (hbottom : s.bottom = a) (hright : s.right = p)
    (hleft : s.left = 0) (htop : s.top = 0) (hdiag : s.diagonal = 0)
    (hlower : s.lowerHomotopy = 0) (hupper : s.upperHomotopy = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square := by
  have hz : Z = moduleZero A D := by
    have hh := congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 0 => x.obj 0) hZ
    exact congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)) hh
  subst Z
  let q := _root_.SerrePositivity.DifferentialGraded.moduleConeDesc A D a p hap
  have heq : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData A D a).postcompose q = s := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.ext
    · exact hbottom.symm
    · exact hleft.symm
    · exact (_root_.SerrePositivity.DifferentialGraded.moduleConeDesc_inr A D a p hap).trans hright.symm
    · simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.postcompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData, zero_comp] using
      htop.symm
    · simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.postcompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData, zero_comp] using
      hdiag.symm
    · exact (dgModuleSplitConeDesc_inl A D a p hap).trans hlower.symm
    · change _root_.SerrePositivity.DifferentialGraded.compose A _ 0 _ = s.upperHomotopy
      rw [hupper]
      apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext A D
      intro x
      rw [_root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π, map_zero, map_zero]
      exact Cochain.zero_comp _ _
  rw [← heq]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isPushout_postcompose_of_homotopy
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSplitConeDesc_homotopy_isIso A D a r b p har hbp hap hs
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData_square]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A D a

/-- 概要：任意の native 零頂点を零角に持つ分裂四角形の cofiber 性。
方針：同じ零二胞体を保つ零角変更を経由し、全四角形の関手同型で戻す。
規約：零加群との厳密等号も対象ごとの零複体性も要求しない。
使われ方：K-B の元のラベル作用による native 分裂四角形。 -/
lemma dgModuleSplitSquare_isPushout
    (a : M ⟶ N) (r : N ⟶ M) (b : P ⟶ N) (p : N ⟶ P)
    (har : a ≫ r = 𝟙 M) (hbp : b ≫ p = 𝟙 P) (hap : a ≫ p = 0)
    (hbr : b ≫ r = 0) (hs : r ≫ a + p ≫ b = 𝟙 N)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D M N Z P)
    (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) Z)))
    (hbottom : s.bottom = a) (hright : s.right = p)
    (hleft : s.left = 0) (htop : s.top = 0) (hdiag : s.diagonal = 0)
    (hlower : s.lowerHomotopy = 0) (hupper : s.upperHomotopy = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square := by
  have hf : (0 : Z ⟶ _root_.SerrePositivity.DifferentialGraded.moduleZero A D) ≫ (0 : _root_.SerrePositivity.DifferentialGraded.moduleZero A D ⟶ P) = s.top := by
    rw [zero_comp, htop]
  let t := s.changeTopMiddle (0 : Z ⟶ _root_.SerrePositivity.DifferentialGraded.moduleZero A D) 0 hf
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square := by
    apply dgModuleSplitSquare_isPushout_of_zeroVertex_eq A D a r b p har hbp hap hbr hs t
    · rfl
    · exact hbottom
    · exact hright
    · change s.left ≫ (0 : Z ⟶ _root_.SerrePositivity.DifferentialGraded.moduleZero A D) = 0
      rw [hleft, zero_comp]
    · rfl
    · exact hdiag
    · exact hlower
    · exact hupper
  have hz₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 0 1) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.square_vertex01]
    exact hZ
  have hz₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 1) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.square_vertex01]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A D
  exact ht.of_functorIso (s.changeTopMiddleFunctorIso 0 0 hf hz₀ hz₁).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
