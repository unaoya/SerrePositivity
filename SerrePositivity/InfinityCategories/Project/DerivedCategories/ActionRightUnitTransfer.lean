module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationHomNaturality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
/-!
概要：指定合成子・単位・比較の正方形から、右単位三角式を同じ実作用へ移す。
方針：全関手同型の実交換則と同じ指定値の等式を使う。
規約：新しい比較を選ばない。使われ方：元の導来 kernel 合成子の coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
private lemma precomp_identity {X Y : SSet.{u}} {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    e.precomp (𝟙 X) = e := Iso.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_id_hom e)
/-- 同じ指定比較の各正方形は、元の実作用の右単位三角式を前合成後に与える。 -/
lemma rightUnitComparison_transfer {X A Y B : SSet.{u}}
    [Quasicategory X] [Quasicategory B]
    (L : X ⟶ A) (M : Y ⟶ B) (V : X ⟶ X) (U : A ⟶ A)
    (F T : A ⟶ B) (G H : X ⟶ Y)
    (xU : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ U) (V ≫ L))
    (xF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ F) (G ≫ M)) (xT : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ T) (H ≫ M))
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (U ≫ F) T) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (V ≫ G) H)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T F) (e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso H G)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso U (𝟙 A)) (u : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso V (𝟙 X))
    (hc : k.precomp L ≪≫ xT = xU.postcomp F ≪≫ xF.precomp V ≪≫ a.postcomp M)
    (hn : xT ≪≫ e₀.postcomp M = e.precomp L ≪≫ xF)
    (hu : xU ≪≫ u.postcomp L = v.precomp L) (ht : a ≪≫ e₀ = u.postcomp G) :
    k.precomp L ≪≫ e.precomp L = (v.postcomp F).precomp L := by
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange u xF
  rw [precomp_identity] at hx
  have hh : (k.precomp L ≪≫ e.precomp L) ≪≫ xF = (v.postcomp F).precomp L ≪≫ xF := by
    calc
      _ = k.precomp L ≪≫ (e.precomp L ≪≫ xF) := Iso.trans_assoc _ _ _
      _ = k.precomp L ≪≫ (xT ≪≫ e₀.postcomp M) := by rw [← hn]
      _ = (k.precomp L ≪≫ xT) ≪≫ e₀.postcomp M := (Iso.trans_assoc _ _ _).symm
      _ = (xU.postcomp F ≪≫ xF.precomp V ≪≫ a.postcomp M) ≪≫ e₀.postcomp M := by rw [hc]
      _ = xU.postcomp F ≪≫ xF.precomp V ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (a ≪≫ e₀) M := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
        simp only [Iso.trans_assoc]
      _ = xU.postcomp F ≪≫ xF.precomp V ≪≫ (u.postcomp G).postcomp M := by rw [ht]
      _ = (xU.postcomp F ≪≫ (u.postcomp L).postcomp F) ≪≫ xF := by
        simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp, Iso.trans_assoc] using
          congrArg (fun z => xU.postcomp F ≪≫ z) hx.symm
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (xU ≪≫ u.postcomp L) F ≪≫ xF := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
      _ = (v.precomp L).postcomp F ≪≫ xF := by rw [hu]
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  apply Iso.ext
  exact (cancel_mono xF.hom).mp (congrArg Iso.hom hh)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
