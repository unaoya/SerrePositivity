module

public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-!
# 右 pinched Hom の端点の等式による移送

概要：端点の等式で pinched Hom を同定し、台の単体とホモトピー同値性の不変性を示す。
方針：端点の等式を消去して恒等の同型に帰着する。
規約：頂点同型ではなく頂点の等式に沿う移送を扱う。
使われ方：HA 1.3.1.17、Kerodon 2.5.9 の実際の pinchedHomMap と固定端点の比較射の接続。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory
open scoped Simplicial

/-- 概要：二端点の等式は右 pinched Hom の自然同型を与える。
方針：二端点を引数とする単体集合の等式を同型にする。
規約：始域と終域は同じ元の単体集合の写像空間。
使われ方：Kerodon 2.5.9 の比較写像の端点の表示をそろえる。 -/
def pinchedEndpointIso {X : SSet.{u}} {x y x' y' : X _⦋0⦌} (hx : x = x') (hy : y = y') :
    pinchedHom x y ≅ pinchedHom x' y' :=
  eqToIso (congrArg₂ (fun a b : X _⦋0⦌ ↦ pinchedHom a b) hx hy)

/-- 概要：端点の等式に沿って移送しても pinched 単体の台の単体は変わらない。
方針：端点の等式を消去して同型が恒等となることを使う。
規約：全次数での元の単体集合の単体の等式。
使われ方：HA 1.3.1.17 の二つの pinched Hom の比較射の同定。 -/
lemma pinchedEndpointIso_hom_val {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') {n : ℕ} (s : (pinchedHom x y) _⦋n⦌) :
    (((pinchedEndpointIso hx hy).hom).app _ s).val = s.val := by
  subst x' y'
  rfl

/-- 概要：端点の等式による後合成は実際の単体的ホモトピー逆の存在を変えない。
方針：等式を消去し、恒等射との後合成を取り除く。
規約：Kan 性や追加の充填仮定は不要。
使われ方：Kerodon 2.5.9 の固定端点の比較射から Core の判定への移送。 -/
lemma pinchedEndpointIso_postcomp_iff {A X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') (f : A ⟶ pinchedHom x y) :
    IsSimplicialHomotopyEquivalence (f ≫ (pinchedEndpointIso hx hy).hom) ↔
      IsSimplicialHomotopyEquivalence f := by
  subst x' y'
  change IsSimplicialHomotopyEquivalence (f ≫ 𝟙 _) ↔ _
  rw [Category.comp_id]

end SerrePositivity.InfinityCategories.DoldKanComparison
