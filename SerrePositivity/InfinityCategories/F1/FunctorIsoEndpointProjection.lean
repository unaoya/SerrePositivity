module

public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransport

/-!
概要：指定関手同型の端点正規化は、後合成が回収する等号の同型を保持する。
方針：端点の等号を消去し、証明の非依存性を使う。
規約：指定された同型と射影を保持する。
使われ方：fiber 内比較と切断の単位比較を同じ端点で照合する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 端点の表示を変更しても、射影後の等号同型は同じ端点の等号同型となる。 -/
lemma functorIsoOfEq_postcomp_eqToIso {A E B : SSet.{u}}
    {f g f' g' : A ⟶ E} (e : FunctorIso f g) (hf : f = f') (hg : g = g')
    (p : E ⟶ B) (h : f ≫ p = g ≫ p) (h' : f' ≫ p = g' ≫ p)
    (he : e.postcomp p = eqToIso (congrArg
      (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (functorVertex v)) h)) :
    (F2.functorIsoOfEq e hf hg).postcomp p = eqToIso (congrArg
      (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (functorVertex v)) h') := by
  subst f' g'
  exact he

/-- 端点だけの正規化後に前合成しても、指定された元の同型の値を保持する。 -/
lemma functorIsoOfEq_precomp_heq {A E K : SSet.{u}}
    {f g f' g' : A ⟶ E} (e : FunctorIso f g) (hf : f = f') (hg : g = g')
    (r : K ⟶ A) :
    HEq ((F2.functorIsoOfEq e hf hg).precomp r) (e.precomp r) := by
  subst f' g'
  rfl

end SerrePositivity.InfinityCategories
