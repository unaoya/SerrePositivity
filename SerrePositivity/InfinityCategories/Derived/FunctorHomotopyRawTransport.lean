module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
/-!
概要：円柱射の比較と前合成を、指定された全関手射へ移す。
方針：端点等式を消去し、同じ実ホモトピーの代表辺を保持する。
規約：頂点成分の一致で代用しない。使われ方：augmentation の通常後続像の計算。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
/-- 明示した端点等式の下で同じ指定同型の順方向射を型付きで比較する。 -/
lemma functorIso_hom_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (he : HEq e e') : HEq e.hom e'.hom := by
  subst f' g'
  cases eq_of_heq he
  rfl
/-- 円柱射が等しい二つの全単体ホモトピーは、同じ全関手射の類を与える。 -/
lemma functorHomotopyHom_heq_of_raw_eq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g') (h : H.h = H'.h) :
    HEq (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H')) := by
  have hf : f = f' := by rw [← H.h₀, h, H'.h₀]
  have hg : g = g' := by rw [← H.h₁, h, H'.h₁]
  subst f' g'
  have hh : H = H' := by
    cases H
    cases H'
    cases h
    rfl
  cases hh
  rfl

/-- 指定ホモトピーの類を持つ関手同型の前合成は、同じ円柱の前合成を回収する。 -/
lemma functorIso_precomp_hom_of_homotopy {X Y W : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (A : SSet.Homotopy f g) (S : W ⟶ X)
    (he : e.hom = Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy A)) :
    (e.precomp S).hom = Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp A S)) := by
  rw [F2.functorIso_precomp_hom, he]
  exact (functorHomotopyPrecomp_hom A S).symm
end SerrePositivity.InfinityCategories
