module

public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：端点の等式による表示変更と、選んだホモトピー代表の類を比較する。
方針：異なる型付き端点の射を Arrow の対象として比較する。
規約：代表の raw な等式と h Fun の類の等式を区別する。
使われ方：相対 join の端点補正の自然変換の類の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同型の両端の図式を厳密な等式で書き換える。
方針：二つの等式による輸送。
規約：新しい同型を選ばない。
使われ方：円柱比較の両端への同時の制限。 -/
def kanFunctorIsoTransport {A X : SSet.{u}} {U V U' V' : A ⟶ X}
    (e : FunctorIso U V) (hU : U = U') (hV : V = V') : FunctorIso U' V' :=
  hU ▸ hV ▸ e

/-- 概要：端点を輸送しても Arrow の対象としての同型の順方向の射は変わらない。
方針：端点の等式を消去する。
規約：始域と終域の型付き表示が違っていてよい。
使われ方：前合成による比較で端点の書き換えを吸収する。 -/
lemma kanFunctorIsoTransport_hom_arrow {A X : SSet.{u}} {U V U' V' : A ⟶ X}
    (e : FunctorIso U V) (hU : U = U') (hV : V = V') :
    Arrow.mk (kanFunctorIsoTransport e hU hV).hom = Arrow.mk e.hom := by
  subst U' V'
  rfl

/-- 概要：同型の選んだホモトピー代表の類は元の同型の射。
方針：任意の関手圏の射についての代表の仕様を適用する。
規約：可逆性の証明とは独立に代表の類を計算する。
使われ方：両端で選び直した代表と円柱比較の制限の比較。 -/
lemma kanFunctorIso_simplicialHomotopy_hom {A X : SSet.{u}} [Quasicategory X]
    {U V : A ⟶ X} (e : FunctorIso U V) :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy e.simplicialHomotopy) = e.hom :=
  functorHomHomotopy_hom e.hom

/-- 概要：端点の表示が違っても raw なホモトピーが同じなら Arrow としての類は同じ。
方針：curry した一次単体の一致を一般の Arrow 比較へ渡す。
規約：型付きホモトピーそのものの等式は要求しない。
使われ方：正方形の側辺を前合成した代表として認識する。 -/
lemma kanFunctorHomotopy_hom_arrow_of_h_eq {A X : SSet.{u}}
    {U V U' V' : A ⟶ X} (H : SSet.Homotopy U V) (H' : SSet.Homotopy U' V')
    (h : H.h = H'.h) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy H')) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  change SSet.yonedaEquiv (curry H.h) = SSet.yonedaEquiv (curry H'.h)
  rw [h]

/-- 概要：異なる端点表示を含む類の等式は前合成で保存される。
方針：h Fun の前合成関手を Arrow 圏へ持ち上げる。
規約：ホモトピーの代表を選び直さない。
使われ方：両端の同時の類の比較を左右各辺へ制限する。 -/
lemma kanFunctorHomotopy_precomp_hom_arrow {A B X : SSet.{u}}
    {U V U' V' : B ⟶ X} (H : SSet.Homotopy U V) (H' : SSet.Homotopy U' V')
    (h : Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy H)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy H'))) (i : A ⟶ B) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H i))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H' i))) := by
  rw [functorHomotopyPrecomp_hom, functorHomotopyPrecomp_hom]
  exact congrArg (hoFunctor.map ((pre i).app X)).toFunctor.mapArrow.obj h

end SerrePositivity.InfinityCategories
