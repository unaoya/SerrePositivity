module
public import SerrePositivity.InfinityCategories.Derived.ResolutionSourceHomNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
/-!
概要：出力を恒等へ写す同じ全関手変換に対し、指定出力比較の自然性を証明する。
方針：元の入力比較の自然性を出力へ送り、恒等像を全関手射として消去する。
規約：指定比較と両方の指定逆を保つ。使われ方：分解変更の実射作用との同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma qCatResolutionOutputPrecompIso_hom_naturality
    {X Y A B T : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory B] [Quasicategory T]
    (Q : QCatEquivalence X A) (S : QCatEquivalence Y B)
    (h k : A ⟶ B) (H K : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (hs : H ≫ S.hom = Q.hom ≫ h) (ks : K ≫ S.hom = Q.hom ≫ k)
    (hr : H ≫ RY = RX) (kr : K ≫ RY = RX)
    (a : FunctorHom h k) (ε : FunctorHom H K)
    (he : HEq (functorHomPostcomp H K S.hom ε) (functorHomPrecomp h k Q.hom a))
    (hε : HEq (functorHomPostcomp H K RY ε)
      (𝟙 (HomotopyCategory.mk (functorVertex RX)))) :
    (qCatResolutionOutputPrecompIso Q S h H RX RY hs hr).hom ≫
        functorHomPostcomp h k (S.inv ≫ RY) a =
      (qCatResolutionOutputPrecompIso Q S k K RX RY ks kr).hom := by
  let d := qCatResolutionSourceComparisonIso Q S h H hs
  let t := qCatResolutionSourceComparisonIso Q S k K ks
  let e := qCatResolutionOutputPrecompIso Q S h H RX RY hs hr
  let b := qCatResolutionOutputPrecompIso Q S k K RX RY ks kr
  have hf : Q.inv ≫ RX = (Q.inv ≫ H) ≫ RY := by rw [Category.assoc, hr]
  have hg : h ≫ S.inv ≫ RY = (h ≫ S.inv) ≫ RY := (Category.assoc _ _ _).symm
  have hh : Q.inv ≫ RX = (Q.inv ≫ K) ≫ RY := by rw [Category.assoc, kr]
  have hk : k ≫ S.inv ≫ RY = (k ≫ S.inv) ≫ RY := (Category.assoc _ _ _).symm
  have hc : HEq e.hom
      (functorHomPostcomp (Q.inv ≫ H) (h ≫ S.inv) RY d.hom) := by
    have h₀ := functorIso_hom_heq_of_endpoint_heq e (d.postcomp RY) hf hg
      (qCatResolutionOutputPrecompIso_sourceComparison_heq Q S h H RX RY hs hr)
    exact h₀.trans (heq_of_eq (functorIso_postcomp_hom_typed d RY))
  have hd : HEq b.hom
      (functorHomPostcomp (Q.inv ≫ K) (k ≫ S.inv) RY t.hom) := by
    have h₀ := functorIso_hom_heq_of_endpoint_heq b (t.postcomp RY) hh hk
      (qCatResolutionOutputPrecompIso_sourceComparison_heq Q S k K RX RY ks kr)
    exact h₀.trans (heq_of_eq (functorIso_postcomp_hom_typed t RY))
  have hm : functorHomPrecomp RX RX Q.inv
      (𝟙 (HomotopyCategory.mk (functorVertex RX))) =
      𝟙 (HomotopyCategory.mk (functorVertex (Q.inv ≫ RX))) :=
    CategoryTheory.Functor.map_id _ _
  have hq : HEq
      (functorHomPostcomp (Q.inv ≫ H) (Q.inv ≫ K) RY
        (functorHomPrecomp H K Q.inv ε))
      (𝟙 (HomotopyCategory.mk (functorVertex (Q.inv ≫ RX)))) := by
    have h₀ := heq_of_eq (functorHomPrecomp_postcomp H K Q.inv RY ε)
    have h₁ := functorHom_precomp_heq (functorHomPostcomp H K RY ε)
      (𝟙 (HomotopyCategory.mk (functorVertex RX))) hr kr hε Q.inv
    exact h₀.trans (h₁.trans (heq_of_eq hm))
  have hn := congrArg
    (fun z : FunctorHom (Q.inv ≫ H) (k ≫ S.inv) =>
      functorHomPostcomp (Q.inv ≫ H) (k ≫ S.inv) RY z)
    (qCatResolutionSourceComparisonIso_hom_naturality Q S h k H K hs ks a ε he)
  have hn' :
      functorHomPostcomp (Q.inv ≫ H) (h ≫ S.inv) RY d.hom ≫
        functorHomPostcomp (h ≫ S.inv) (k ≫ S.inv) RY
          (functorHomPostcomp h k S.inv a) =
      functorHomPostcomp (Q.inv ≫ H) (Q.inv ≫ K) RY
        (functorHomPrecomp H K Q.inv ε) ≫
        functorHomPostcomp (Q.inv ≫ K) (k ≫ S.inv) RY t.hom := by
    simpa only [functorHomPostcomp_comp] using! hn
  have hp := functorHom_two_two_eq_of_heq
    e.hom (functorHomPostcomp h k (S.inv ≫ RY) a)
    (𝟙 (HomotopyCategory.mk (functorVertex (Q.inv ≫ RX)))) b.hom
    (functorHomPostcomp (Q.inv ≫ H) (h ≫ S.inv) RY d.hom)
    (functorHomPostcomp (h ≫ S.inv) (k ≫ S.inv) RY
      (functorHomPostcomp h k S.inv a))
    (functorHomPostcomp (Q.inv ≫ H) (Q.inv ≫ K) RY
      (functorHomPrecomp H K Q.inv ε))
    (functorHomPostcomp (Q.inv ≫ K) (k ≫ S.inv) RY t.hom)
    hf hg hh hk hc
    (heq_of_eq (functorHomPostcomp_postcomp h k S.inv RY a)).symm hq.symm hd hn'
  simpa only [Category.id_comp] using! hp
end SerrePositivity.InfinityCategories
