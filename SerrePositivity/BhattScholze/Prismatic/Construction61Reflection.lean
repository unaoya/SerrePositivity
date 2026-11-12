module

public import SerrePositivity.BhattScholze.Prismatic.Construction61Detection
public import SerrePositivity.HomologicalAlgebra.CompleteCochainCone
public import SerrePositivity.HomologicalAlgebra.SemifreeBaseChangeModel

/-!
# 結晶被覆の完備底変換は擬同型を反映する

## 概要
非有界な K-flat 模型上で、結晶被覆への完備底変換が擬同型を反映する。

## 方針
係数拡大の写像錐比較と完備化の三角関手性により、零性の反映を写像錐へ適用する。

## 規約
BS 著者版 Proposition 6.2、Theorem 6.3 の帰着の入力。HT 比較の組み立てを含めない。

## 使われ方
通常の導来テンソルを計算する半自由模型上で、一般の射の比較を検出する。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.BhattScholze.Prismatic.Construction61
open CategoryTheory CategoryTheory.Limits DifferentialGraded DerivedCompletion InfinityCategories
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 概要：結晶被覆への完備底変換は非有界な K-flat 模型上の擬同型を反映する。
方針：実際の係数拡大の写像錐同型と完備化の三角関手性から、錐の零性を反映する。
規約：BS 著者版 Proposition 6.2、D77。両模型の前後の K-flat 性を明示する。
使われ方：半自由分解により任意の非有界な導来入力へ適用する。 -/
theorem quasiIso_of_completedCover_map_quasiIso
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L)
    (hK : complexKFlat A K) (hL : complexKFlat A L)
    (hBK : complexKFlat (crystallineCoverRing P) (baseChange (crystallineCoverMap P).toRingHom K))
    (hBL : complexKFlat (crystallineCoverRing P) (baseChange (crystallineCoverMap P).toRingHom L))
    (hpK : IsComplete A (p : A) (DerivedCategory.Q.obj K))
    (hpL : IsComplete A (p : A) (DerivedCategory.Q.obj L))
    (hdK : IsComplete A P.generator (DerivedCategory.Q.obj K))
    (hdL : IsComplete A P.generator (DerivedCategory.Q.obj L))
    (hf : QuasiIso ((completedCoverModelFunctor P).map f)) : QuasiIso f := by
  let B := crystallineCoverRing P
  let b := (crystallineCoverMap P).toRingHom
  let E := ModuleCat.extendScalars b
  let G := E.mapHomologicalComplex (.up ℤ)
  let C := complexCompletionFunctor B (p : B)
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso f E
  have hc : complexKFlat B (baseChange b (CochainComplex.mappingCone f)) := by
    exact complexKFlat_of_iso B e (complexKFlat_cone B (G.map f) hBK hBL)
  have hz : ∀ i : ℤ, IsZero ((C.obj (C.obj
      (baseChange b (CochainComplex.mappingCone f)))).homology i) := by
    intro i
    have h₀ := repeatedCompletion_cone_homology_isZero_of_map_quasiIso
      (p : B) (G.map f) hf i
    exact h₀.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (C.mapIso (C.mapIso e)))
  have hcone := cochain_acyclic_of_completedCover_acyclic P hF hR
    (CochainComplex.mappingCone f) (complexKFlat_cone A f hK hL) hc
    (isComplete_Q_mappingCone A (p : A) f hpK hpL)
    (isComplete_Q_mappingCone A P.generator f hdK hdL) hz
  apply (SerrePositivity.cochain_quasiIso_iff_cone_acyclic f).mpr
  intro i
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ i).mpr (hcone i)

/-- 概要：任意の半自由模型間の射について、完備底変換は擬同型を反映する。
方針：半自由性から前後の K-flat 性を供給し、上の検出を使う。
規約：BS 著者版 Proposition 6.2、非有界な複体。
使われ方：分解上で計算する一般の導来写像の比較。 -/
theorem quasiIso_of_completedCover_semifree_map_quasiIso
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L)
    (hK : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A K) (hL : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A L)
    (hpK : IsComplete A (p : A) (DerivedCategory.Q.obj K))
    (hpL : IsComplete A (p : A) (DerivedCategory.Q.obj L))
    (hdK : IsComplete A P.generator (DerivedCategory.Q.obj K))
    (hdL : IsComplete A P.generator (DerivedCategory.Q.obj L))
    (hf : QuasiIso ((completedCoverModelFunctor P).map f)) : QuasiIso f :=
  quasiIso_of_completedCover_map_quasiIso P hF hR f
    (semifreeComplex_isKFlat hK) (semifreeComplex_isKFlat hL)
    (semifreeComplex_baseChange_isKFlat (crystallineCoverMap P).toRingHom hK)
    (semifreeComplex_baseChange_isKFlat (crystallineCoverMap P).toRingHom hL) hpK hpL hdK hdL hf

/-- 概要：普遍 prism の被覆の完備底変換も、非有界な半自由模型間の擬同型を反映する。
方針：K2 の二つの入力を直接、半自由模型の検出へ入れる。
規約：BS 著者版 Proposition 6.2、Theorem 6.3、D77。
使われ方：普遍基底上の比較射の検出。 -/
theorem universal_quasiIso_of_completedCover_map_quasiIso
    {K L : CochainComplex (ModuleCat.{u} (UniversalOrientedPrismRing.{u} p)) ℤ}
    (f : K ⟶ L) (hK : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree _ K) (hL : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree _ L)
    (hpK : IsComplete _ (p : UniversalOrientedPrismRing.{u} p) (DerivedCategory.Q.obj K))
    (hpL : IsComplete _ (p : UniversalOrientedPrismRing.{u} p) (DerivedCategory.Q.obj L))
    (hdK : IsComplete _ (universalOrientedPrism.{u} p).generator (DerivedCategory.Q.obj K))
    (hdL : IsComplete _ (universalOrientedPrism.{u} p).generator (DerivedCategory.Q.obj L))
    (hf : QuasiIso ((completedCoverModelFunctor (universalOrientedPrism.{u} p)).map f)) :
    QuasiIso f :=
  quasiIso_of_completedCover_semifree_map_quasiIso (universalOrientedPrism.{u} p)
    (universalOrientedPrism_frobenius_isCompletelyFlat p)
    (universalOrientedPrism_mod_generator_p_regular p) f hK hL hpK hpL hdK hdL hf

/-- 概要：完備な半自由模型間の射は、被覆への完備底変換の前後で擬同型性が同値。
方針：反映には完備 Nakayama、保存には半自由模型間の底変換の不変性を使う。
規約：BS 著者版 Proposition 6.2、非有界な模型。
使われ方：実際に導来テンソルを計算する模型上の保存性と保存的性。 -/
theorem completedCover_semifree_map_quasiIso_iff
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L)
    (hK : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A K) (hL : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A L)
    (hpK : IsComplete A (p : A) (DerivedCategory.Q.obj K))
    (hpL : IsComplete A (p : A) (DerivedCategory.Q.obj L))
    (hdK : IsComplete A P.generator (DerivedCategory.Q.obj K))
    (hdL : IsComplete A P.generator (DerivedCategory.Q.obj L)) :
    QuasiIso ((completedCoverModelFunctor P).map f) ↔ QuasiIso f := by
  constructor
  · exact quasiIso_of_completedCover_semifree_map_quasiIso P hF hR f hK hL hpK hpL hdK hdL
  · intro hf
    letI := hf
    let B := crystallineCoverRing P
    let E := (ModuleCat.extendScalars (crystallineCoverMap P).toRingHom).mapHomologicalComplex (.up ℤ)
    letI := semifreeBaseChange_map_quasiIso (crystallineCoverMap P).toRingHom f hK hL
    letI := complexCompletionFunctor_map_quasiIso B (p : B) (E.map f)
    exact complexCompletionFunctor_map_quasiIso B (p : B)
      ((complexCompletionFunctor B (p : B)).map (E.map f))

end SerrePositivity.BhattScholze.Prismatic.Construction61
