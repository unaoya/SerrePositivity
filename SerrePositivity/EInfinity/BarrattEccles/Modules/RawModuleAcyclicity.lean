module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleGenerators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleDiskCoverAcyclic

/-!
# 実 disk 被覆による自由 J-cell の非輪状性

概要：N01 の右転送に必要な非輪状性を、既存の実 disk 被覆で証明する。
方針：全射の左類の射を、非輪状直和項への包含の retract とする。
規約：固定底の平坦性・cofibrancy とモデル構造の存在を仮定しない。
使われ方：Keller, On differential graded categories, Theorem 3.2 (1) の右転送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A]

/-- 概要：非輪状な第二加群への直和包含は元の擬同型。
方針：既存の第一射影の擬同型性と片側逆を使う。
規約：同じ実直和。使われ方：全射の左類の retract。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleBiprodInl_quasiIso (X : (operad A).Algebra)
    (M K : strictRawModuleCategory A X)
    (hK : moduleAcyclic A (dgAlgebraCategory A ((assocForget A).obj X)) K) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      (moduleBiprodInl A _ M K) := by
  intro x
  let U := moduleEvaluation A (dgAlgebraCategory A ((assocForget A).obj X)) x
  have : QuasiIso (biprod.fst : U.obj M ⊞ U.obj K ⟶ U.obj M) :=
    complexBiprod_fst_quasiIso_of_acyclic A (U.obj M) (U.obj K) (hK x)
  rw [moduleBiprodInl_eval]
  have : QuasiIso ((biprod.inl : U.obj M ⟶ U.obj M ⊞ U.obj K) ≫
      (biprod.fst : U.obj M ⊞ U.obj K ⟶ U.obj M)) := by
    rw [biprod.inl_fst]
    infer_instance
  exact quasiIso_of_comp_right (biprod.inl : U.obj M ⟶ U.obj M ⊞ U.obj K)
    (biprod.fst : U.obj M ⊞ U.obj K ⟶ U.obj M)

/-- 概要：台の全射への左持ち上げ性を持つ射は同じ擬同型。
方針：終域の実非輪状 disk 被覆を直和し、その包含の retract とする。
規約：モデル構造を先取りしない。使われ方：自由 J の生成左類の非輪状性。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleFibrations_llp_quasiIso (X : (operad A).Algebra)
    {M N : strictRawModuleCategory A X} (f : M ⟶ N)
    (hf : ((_root_.SerrePositivity.ProjectiveModel.projectiveFibrations A).inverseImage (strictRawModuleUnderlying X)).llp f) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) f := by
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  let K := moduleDiskCover A D N
  let B := moduleBiprod A D M K
  let i : M ⟶ B := moduleBiprodInl A D M K
  let p : B ⟶ N := moduleBiprodFst A D M K ≫ f +
    moduleBiprodSnd A D M K ≫ moduleDiskCoverπ A D N
  have hip : i ≫ p = f := by
    dsimp only [i, p]
    rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
    have h₁ : moduleBiprodInl A D M K ≫ moduleBiprodFst A D M K = 𝟙 M :=
      (moduleBinaryBicone A D M K).inl_fst
    have h₂ : moduleBiprodInl A D M K ≫ moduleBiprodSnd A D M K = 0 :=
      (moduleBinaryBicone A D M K).inl_snd
    rw [h₁, h₂]
    simp only [Category.id_comp, zero_comp, add_zero]

  have hp : (_root_.SerrePositivity.ProjectiveModel.projectiveFibrations A).inverseImage (strictRawModuleUnderlying X) p := by
    intro n y
    obtain ⟨z, hz⟩ := moduleDiskCoverπ_degreewiseSurjective A D N
      (Opposite.op DGAlgebraPoint.star) n y
    let U := strictRawModuleUnderlying X
    refine ⟨((U.map (moduleBiprodInr A D M K)).f n) z, ?_⟩
    have he : moduleBiprodInr A D M K ≫ p = moduleDiskCoverπ A D N := by
      dsimp only [p]
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
      have h₁ : moduleBiprodInr A D M K ≫ moduleBiprodFst A D M K = 0 :=
        (moduleBinaryBicone A D M K).inr_fst
      have h₂ : moduleBiprodInr A D M K ≫ moduleBiprodSnd A D M K = 𝟙 K :=
        (moduleBinaryBicone A D M K).inr_snd
      rw [h₁, h₂]
      simp only [Category.id_comp, zero_comp, zero_add]

    have he' := congrArg (fun q => (U.map q).f n z) he
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
      ModuleCat.comp_apply] using he'.trans hz
  let sq : CommSq i f p (𝟙 N) := ⟨by simpa using hip⟩
  obtain ⟨l⟩ := ((hf p hp).sq_hasLift sq).exists_lift
  have hi := strictRawModuleBiprodInl_quasiIso A X M K (dgModuleDiskCover_acyclic A D N)
  apply MorphismProperty.of_retract (P := moduleQuasiIso A D) ?_ hi
  exact {
    i := Arrow.homMk (𝟙 M) l.l (by simpa using l.fac_left.symm)
    r := Arrow.homMk (𝟙 M) p (by simpa using hip.symm)
    retract := by
      apply Arrow.hom_ext
      · simp
      · exact l.fac_right }

/-- 概要：自由 J の全相対 cell は同じ元の擬同型。
方針：生成左類の閉性と全射の左類の retract 判定を使う。
規約：元の自由射族、同じ基礎宇宙 u。使われ方：N01 の右転送の実入力。
文献：Keller, Theorem 3.2 (1) の構成の成分。 -/
lemma strictRawModuleFreeCells_acyclic (X : (operad A).Algebra) :
    MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u}
        (strictRawModuleGeneratingTrivialCofibrations A X)).pushouts ≤
      moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) := by
  apply le_trans ?_ (fun _ _ f hf => strictRawModuleFibrations_llp_quasiIso A X f hf)
  rw [← strictRawModuleGeneratingTrivialCofibrations_rlp A X,
    MorphismProperty.transfiniteCompositions_le_iff, MorphismProperty.pushouts_le_iff,
    MorphismProperty.coproducts_le_iff]
  exact MorphismProperty.le_llp_rlp _

end SerrePositivity.EInfinity.BarrattEccles
