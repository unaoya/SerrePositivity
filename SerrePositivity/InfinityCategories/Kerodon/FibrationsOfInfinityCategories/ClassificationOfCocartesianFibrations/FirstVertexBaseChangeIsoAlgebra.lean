module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CurryPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiagramIsoNormalizationAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：指定初頂点四角形の端点移送と同型の合成を一度だけ計算する。
方針：前合成の合成則・diagramIsoCongrの合成則と既存の同型の相殺を使う。
規約：HTT §3.3.2・Kerodon Tag 028Tの構成に付随する、このモデルの特殊な法則。
使われ方：P3-Dで具体的な大きい同型を展開せず、元の全族の式へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ端点の恒等移送は指定同型を保つ。 -/
private lemma congr_refl {A X : SSet.{u}} {f g : A ⟶ X} (e : FunctorIso f g) :
    diagramIsoCongr rfl rfl e = e := by
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 前合成射の同じ等式を始点側と終点側のどちらへ入れても一致する。 -/
private lemma precomp_base_congr {A B X : SSet.{u}} {F G : B ⟶ X}
    (e : FunctorIso F G) {p q : A ⟶ B} (h : p = q) :
    diagramIsoCongr rfl (congrArg (fun z => z ≫ G) h) (e.precomp p) =
      diagramIsoCongr (congrArg (fun z => z ≫ F) h.symm) rfl (e.precomp q) := by
  subst q
  simp only [congr_refl]

/-- 同じ同型の族の添字の等式で終端を移すと、元の同型との合成は保たれる。 -/
lemma diagramIsoCongr_family_comp {A X : SSet.{u}} {Z : Type v}
    {F H : A ⟶ X} (G : Z → (A ⟶ X)) (a : ∀ z, FunctorIso H (G z))
    {r s : Z} (h : r = s) (e : FunctorIso F H) :
    diagramIsoCongr rfl (congrArg G h) (e ≪≫ a r) = e ≪≫ a s := by
  cases h
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 指定初頂点四角形の正規化された係数照合を、元の同じ全同型の式へ戻す。
HTT §3.3.2・Kerodon Tag 028Tの構成に付随する、この模型の合成・移送の法則。 -/
@[cite HTT "3.3.2" (partial := special) "指定初頂点四角形に沿う同型の合成と端点移送の計算則。"]
lemma firstVertexBaseChange_isoAlgebra {B D K L X : SSet.{u}}
    (i : K ⟶ B) (j : L ⟶ D) (t : L ⟶ K) (k : D ⟶ B) (h : t ≫ i = j ≫ k)
    (F : B ⟶ X) (G : D ⟶ X) (T : B ⟶ X) (P : K ⟶ X) (Q : L ⟶ X)
    (θp : FunctorIso (i ≫ F) P) (θq : FunctorIso (j ≫ G) Q)
    (β : FunctorIso (k ≫ F) G) (γ : FunctorIso F T)
    (α : FunctorIso P (i ≫ T)) (a : FunctorIso Q (j ≫ k ≫ T))
    (hγ : γ.precomp i = θp ≪≫ α)
    (hA : let hs : j ≫ k ≫ F = t ≫ i ≫ F := congrArg (fun z => z ≫ F) h.symm
      diagramIsoCongr rfl (congrArg (fun z => z ≫ T) h) (α.precomp t) =
        ((θp.precomp t).symm ≪≫ diagramIsoCongr hs rfl (β.precomp j) ≪≫ θq) ≪≫ a) :
    β.precomp j ≪≫ θq ≪≫ a = (γ.precomp k).precomp j := by
  let hs : j ≫ k ≫ F = t ≫ i ≫ F := congrArg (fun z => z ≫ F) h.symm
  let ht := congrArg (fun z => z ≫ T) h
  let b := diagramIsoCongr hs rfl (β.precomp j)
  have hp : (γ.precomp i).precomp t = θp.precomp t ≪≫ α.precomp t := by
    rw [hγ, functorIso_precomp_trans]
  have hpN := congrArg
    (fun z : FunctorIso (t ≫ i ≫ F) (t ≫ i ≫ T) => diagramIsoCongr rfl ht z) hp
  rw [diagramIsoCongr_trans rfl rfl ht, congr_refl] at hpN
  have hb : diagramIsoCongr rfl ht ((γ.precomp i).precomp t) =
      diagramIsoCongr hs rfl ((γ.precomp k).precomp j) := by
    rw [functorIso_precomp_precomp, functorIso_precomp_precomp]
    exact precomp_base_congr γ h
  have hmul : θp.precomp t ≪≫ diagramIsoCongr rfl ht (α.precomp t) = b ≪≫ θq ≪≫ a := by
    calc
      _ = θp.precomp t ≪≫ (((θp.precomp t).symm ≪≫ b ≪≫ θq) ≪≫ a) :=
        congrArg (fun z => θp.precomp t ≪≫ z) hA
      _ = _ := by
        simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  have hn : diagramIsoCongr hs rfl (β.precomp j ≪≫ θq ≪≫ a) =
      diagramIsoCongr hs rfl ((γ.precomp k).precomp j) := by
    rw [diagramIsoCongr_trans_three hs rfl rfl rfl, congr_refl, congr_refl]
    exact hmul.symm.trans (hpN.symm.trans hb)
  exact eq_of_heq ((diagramIsoCongr_heq hs rfl (β.precomp j ≪≫ θq ≪≫ a)).symm.trans
    ((heq_of_eq hn).trans (diagramIsoCongr_heq hs rfl ((γ.precomp k).precomp j))))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
