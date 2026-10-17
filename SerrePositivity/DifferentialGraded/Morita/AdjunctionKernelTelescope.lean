module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelSequence
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseTelescope

/-! # 一般kernel右随伴の可算telescope

## 概要
生成元の関係を順次消す近似列のtelescopeと、そのkernel像から標的への射を構成する。

## 方針
余積保存で各段階の標的射を束ね、三角性とHom完全性でtelescopeへ延長する。

## 規約と注意
局所Hom K-flat性やkernel列の射影性は要求しない。全入力での表現可能性は後続の課題。

## 使われ方
U16aの一般右随伴の表現対象と生成元上のHom同値を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (Y : DerivedModuleCategory A E)

/-- 可算近似の対象族。 -/
abbrev kernelBrownObjects (n : ℕ) := (kernelBrownApproximation A D E K Y n).obj

/-- 近似の可算余積からのkernel像に定まる標的射。 -/
def kernelBrownSumTarget :
    (kernelDerivedTensor A D E K).obj
      (∐ moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟶ Y := by
  let := kernelDerivedTensorPreservesCoproducts A D E (J := ULift.{u} ℕ) K
  exact (PreservesCoproduct.iso (kernelDerivedTensor A D E K)
    (moduleTelescopeFamily A D (kernelBrownObjects A D E K Y))).hom ≫
      Sigma.desc (fun n => (kernelBrownApproximation A D E K Y n.down).target)

/-- 可算余積の各挿入射での標的射の計算。 -/
lemma kernelBrownSumTarget_ι (n : ℕ) :
    (kernelDerivedTensor A D E K).map
        (Sigma.ι (moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟨n⟩) ≫
      kernelBrownSumTarget A D E K Y = (kernelBrownApproximation A D E K Y n).target := by
  let := kernelDerivedTensorPreservesCoproducts A D E (J := ULift.{u} ℕ) K
  dsimp only [kernelBrownSumTarget]
  rw [← ι_comp_sigmaComparison, ← PreservesCoproduct.inv_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]

/-- 三角性から得る実際のkernel作用の加法性。 -/
lemma kernelBrownActionAdditive : (kernelDerivedTensor A D E K).Additive := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  infer_instance

/-- 互換な標的射は1-shiftのkernel像を消す。 -/
lemma kernelBrownSumTarget_relation :
    (kernelDerivedTensor A D E K).map
      (moduleTelescopeMap A D (kernelBrownObjects A D E K Y)
        (kernelBrownTransition A D E K Y)) ≫ kernelBrownSumTarget A D E K Y = 0 := by
  let L := kernelDerivedTensor A D E K
  let : L.Additive := kernelBrownActionAdditive A D E K
  let F := moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)
  let := kernelDerivedTensorPreservesCoproducts A D E (J := ULift.{u} ℕ) K
  apply (isColimitOfHasCoproductOfPreservesColimit L F).hom_ext
  rintro ⟨⟨n⟩⟩
  change L.map (Sigma.ι F ⟨n⟩) ≫ _ = _
  rw [← L.map_comp_assoc]
  have h : Sigma.ι F ⟨n⟩ ≫ moduleTelescopeMap A D
      (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y) =
      Sigma.ι F ⟨n⟩ - kernelBrownTransition A D E K Y n ≫ Sigma.ι F ⟨n+1⟩ := by
    simp only [moduleTelescopeMap, moduleTelescopeShift, comp_sub, Sigma.ι_comp_desc]
    erw [Category.comp_id]
  rw [h, L.map_sub, sub_comp, L.map_comp, Category.assoc]
  change _ = L.map (Sigma.ι F ⟨n⟩) ≫ 0
  erw [kernelBrownSumTarget_ι A D E K Y n,
    kernelBrownSumTarget_ι A D E K Y (n+1), kernelBrownTransition_fac A D E K Y n]
  exact (sub_self _).trans (comp_zero).symm

/-- 近似列のtelescopeとその像からYへの延長射。 -/
structure KernelBrownTelescope where
  obj : DerivedModuleCategory A D
  inclusion : (∐ moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟶ obj
  boundary : obj ⟶ (∐ moduleTelescopeFamily A D (kernelBrownObjects A D E K Y))⟦(1 : ℤ)⟧
  distinguished : Triangle.mk
    (moduleTelescopeMap A D (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y))
    inclusion boundary ∈ distTriang (DerivedModuleCategory A D)
  target : (kernelDerivedTensor A D E K).obj obj ⟶ Y
  fac : (kernelDerivedTensor A D E K).map inclusion ≫ target = kernelBrownSumTarget A D E K Y

/-- 三角性と余積保存から、実際のtelescopeと延長射が存在する。 -/
lemma kernelBrownTelescope_nonempty : Nonempty (KernelBrownTelescope A D E K Y) := by
  let L := kernelDerivedTensor A D E K
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  obtain ⟨Z, c, b, hT⟩ := distinguished_cocone_triangle
    (moduleTelescopeMap A D (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y))
  let T := Triangle.mk
    (moduleTelescopeMap A D (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y)) c b
  obtain ⟨r, hr⟩ := (L.mapTriangle.obj T).yoneda_exact₂ (L.map_distinguished T hT)
    (kernelBrownSumTarget A D E K Y) (kernelBrownSumTarget_relation A D E K Y)
  exact ⟨⟨Z, c, b, hT, r, hr.symm⟩⟩

/-- 構成したtelescopeの一つを選ぶ。 -/
def kernelBrownTelescope : KernelBrownTelescope A D E K Y :=
  Classical.choice (kernelBrownTelescope_nonempty A D E K Y)

variable (S : KernelBrownTelescope A D E K Y)

/-- 各近似段階からtelescopeへの標準射。 -/
def kernelBrownStageMap (n : ℕ) : kernelBrownObjects A D E K Y n ⟶ S.obj :=
  Sigma.ι (moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟨n⟩ ≫ S.inclusion

/-- telescopeの標準射は各段階の標的射を保つ。 -/
lemma kernelBrownStageMap_fac (n : ℕ) :
    (kernelDerivedTensor A D E K).map (kernelBrownStageMap A D E K Y S n) ≫ S.target =
      (kernelBrownApproximation A D E K Y n).target := by
  rw [kernelBrownStageMap, Functor.map_comp, Category.assoc, S.fac,
    kernelBrownSumTarget_ι]

/-- telescopeの標準射は後続射と互換。 -/
lemma kernelBrownStageMap_succ (n : ℕ) :
    kernelBrownTransition A D E K Y n ≫ kernelBrownStageMap A D E K Y S (n+1) =
      kernelBrownStageMap A D E K Y S n := by
  have h := congrArg (fun k =>
    Sigma.ι (moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟨n⟩ ≫ k)
    (comp_distTriang_mor_zero₁₂ _ S.distinguished)
  change _ ≫ (moduleTelescopeMap A D (kernelBrownObjects A D E K Y)
    (kernelBrownTransition A D E K Y) ≫ S.inclusion) = _ at h
  have he : kernelBrownStageMap A D E K Y S n =
      kernelBrownTransition A D E K Y n ≫ kernelBrownStageMap A D E K Y S (n+1) := by
    simpa only [moduleTelescopeMap, moduleTelescopeShift, comp_sub, sub_comp,
      Category.comp_id, Category.assoc, Category.id_comp, Sigma.ι_comp_desc_assoc,
      comp_zero, sub_eq_zero, kernelBrownStageMap] using h
  exact he.symm

end SerrePositivity.DifferentialGraded.Morita
