module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSplitConeHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareHomotopyPostcompose
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeSquareData
public import SerrePositivity.InfinityCategories.Derived.DGModuleConePushout
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareTopMiddleIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareVertices
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Category Limits DifferentialGraded DGNerve
open HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P Z : ModuleCategory A D}

lemma dgModuleSplitConeDesc_inl (a : M ⟶ N) (p : N ⟶ P) (hap : a ≫ p = 0) :
    compose A (x := ForgetEnrichment.to (Complex A) M)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (z := ForgetEnrichment.to (Complex A) P)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeDesc A D a p hap))).val (moduleConeInlElement A D a)
      (add_zero (-1)) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeInlElement_π, ← moduleEvaluation_cochain,
    moduleConeDesc_eval, complexConeDesc_ofHom, map_zero]
  simp

/-- 概要：元の分裂四角形は全右 dg 加群の実 cofiber 四角形。
方針：同じ標準 cone の実二胞体を後合成し、指定係数との厳密一致で輸送する。
規約：零角は native 零頂点で指定し、全 dg 自然な分裂射を使う。
使われ方：K-B の点ごとの分裂 cofiber 性から Perf へ反映する入口。 -/
lemma dgModuleSplitSquare_isPushout_of_zeroVertex_eq
    (a : M ⟶ N) (r : N ⟶ M) (b : P ⟶ N) (p : N ⟶ P)
    (har : a ≫ r = 𝟙 M) (hbp : b ≫ p = 𝟙 P) (hap : a ≫ p = 0)
    (_hbr : b ≫ r = 0) (hs : r ≫ a + p ≫ b = 𝟙 N)
    (s : DGModuleSquareData A D M N Z P)
    (hZ : Simplex.vertex (ForgetEnrichment.to (Complex A) Z) = dgModuleNerveZeroVertex A D)
    (hbottom : s.bottom = a) (hright : s.right = p)
    (hleft : s.left = 0) (htop : s.top = 0) (hdiag : s.diagonal = 0)
    (hlower : s.lowerHomotopy = 0) (hupper : s.upperHomotopy = 0) :
    IsPushoutSquare s.square := by
  have hz : Z = moduleZero A D := by
    have hh := congrArg (fun x : Simplex A (RightModule A D) 0 => x.obj 0) hZ
    exact congrArg (ForgetEnrichment.of (Complex A)) hh
  subst Z
  let q := moduleConeDesc A D a p hap
  have heq : (dgModuleConeSquareData A D a).postcompose q = s := by
    apply DGModuleSquareData.ext
    · exact hbottom.symm
    · exact hleft.symm
    · exact (moduleConeDesc_inr A D a p hap).trans hright.symm
    · simpa only [DGModuleSquareData.postcompose, dgModuleConeSquareData, zero_comp] using
      htop.symm
    · simpa only [DGModuleSquareData.postcompose, dgModuleConeSquareData, zero_comp] using
      hdiag.symm
    · exact (dgModuleSplitConeDesc_inl A D a p hap).trans hlower.symm
    · change compose A _ 0 _ = s.upperHomotopy
      rw [hupper]
      apply moduleHomElement_ext A D
      intro x
      rw [moduleHomCompose_π, map_zero, map_zero]
      exact Cochain.zero_comp _ _
  rw [← heq]
  apply DGModuleSquareData.isPushout_postcompose_of_homotopy
  · exact dgModuleSplitConeDesc_homotopy_isIso A D a r b p har hbp hap hs
  · rw [dgModuleConeSquareData_square]
    exact dgModuleConeSquare_isPushout A D a

/-- 概要：任意の native 零頂点を零角に持つ分裂四角形の cofiber 性。
方針：同じ零二胞体を保つ零角変更を経由し、全四角形の関手同型で戻す。
規約：零加群との厳密等号も対象ごとの零複体性も要求しない。
使われ方：K-B の元のラベル作用による native 分裂四角形。 -/
lemma dgModuleSplitSquare_isPushout
    (a : M ⟶ N) (r : N ⟶ M) (b : P ⟶ N) (p : N ⟶ P)
    (har : a ≫ r = 𝟙 M) (hbp : b ≫ p = 𝟙 P) (hap : a ≫ p = 0)
    (hbr : b ≫ r = 0) (hs : r ≫ a + p ≫ b = 𝟙 N)
    (s : DGModuleSquareData A D M N Z P)
    (hZ : IsZeroVertex (X := dgModuleNerve A D)
      (Simplex.vertex (ForgetEnrichment.to (Complex A) Z)))
    (hbottom : s.bottom = a) (hright : s.right = p)
    (hleft : s.left = 0) (htop : s.top = 0) (hdiag : s.diagonal = 0)
    (hlower : s.lowerHomotopy = 0) (hupper : s.upperHomotopy = 0) :
    IsPushoutSquare s.square := by
  have hf : (0 : Z ⟶ moduleZero A D) ≫ (0 : moduleZero A D ⟶ P) = s.top := by
    rw [zero_comp, htop]
  let t := s.changeTopMiddle (0 : Z ⟶ moduleZero A D) 0 hf
  have ht : IsPushoutSquare t.square := by
    apply dgModuleSplitSquare_isPushout_of_zeroVertex_eq A D a r b p har hbp hap hbr hs t
    · rfl
    · exact hbottom
    · exact hright
    · change s.left ≫ (0 : Z ⟶ moduleZero A D) = 0
      rw [hleft, zero_comp]
    · rfl
    · exact hdiag
    · exact hlower
    · exact hupper
  have hz₀ : IsZeroVertex (squareVertex s.square 0 1) := by
    rw [DGModuleSquareData.square_vertex01]
    exact hZ
  have hz₁ : IsZeroVertex (squareVertex t.square 0 1) := by
    rw [DGModuleSquareData.square_vertex01]
    exact dgModuleNerveZeroVertex_isZero A D
  exact ht.of_functorIso (s.changeTopMiddleFunctorIso 0 0 hf hz₀ hz₁).symm

end SerrePositivity.InfinityCategories
