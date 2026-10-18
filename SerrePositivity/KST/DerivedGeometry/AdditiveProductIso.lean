module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：加法群の圏論的な積と成分ごとの関数の加法群の比較。
方針：射影による明示的な錐の普遍性を使う。
規約：選ばれた圏論的な積を関数型と同一視せず同型で比較する。
使われ方：TT §3・§8、Toën §3.2 の Čech の切断の積との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {ι : Type u} (G : ι → AddCommGrpCat.{u})

/--
概要：成分関数の加法群に射影を備えた積の錐。
方針：各成分への評価の加法準同型を使う。
規約：任意の添字族を扱う。
使われ方：TT §3、Toën §3.2 の Čech 各項。
-/
def additivePiFan : Fan G :=
  Fan.mk (AddCommGrpCat.of (∀ i, G i))
    (fun i => AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i => G i) i))

/--
概要：成分関数の加法群の錐は積の普遍性を持つ。
方針：成分ごとの射を関数値の加法準同型へ束ねる。
規約：極限の存在を仮定のフィールドにしない。
使われ方：TT §3、Toën §3.2 の積の比較同型。
-/
def additivePiFanIsLimit : IsLimit (additivePiFan G) :=
  Fan.IsLimit.mk _
    (fun s => AddCommGrpCat.ofHom (AddMonoidHom.pi (fun i => (s.proj i).hom)))
    (by intro s i; ext x; rfl)
    (by
      intro s m hm
      ext x
      change m x = (fun i => s.proj i x)
      funext i
      exact congrArg (fun f => f x) (hm i))

/--
概要：圏論的な加法群の積と成分関数の加法群の標準同型。
方針：二つの積の錐の普遍性を比較する。
規約：逆写像も積の普遍性から与える。
使われ方：TT §3・§8、Toën §3.2 の Hom と Čech 切断の比較。
-/
def additiveProductIsoPi : (∏ᶜ G) ≅ AddCommGrpCat.of (∀ i, G i) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (additivePiFanIsLimit G)

/--
概要：積の比較同型は各成分への射影と両立する。
方針：積の錐の比較同型の標準の可換性を使う。
規約：実際の圏論的な射の等式。
使われ方：TT §3、Toën §3.2 の Čech 微分の自然性。
-/
lemma additiveProductIsoPi_hom_eval (i : ι) :
    (additiveProductIsoPi G).hom ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i => G i) i) = Pi.π G i :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (Discrete.functor G))
    (additivePiFanIsLimit G) (Discrete.mk i)

/--
概要：積の比較の逆同型を射影すると成分評価になる。
方針：比較同型の射影公式と逆同型の合成を使う。
規約：元の圏論的な射影を保持する。
使われ方：TT §3、Toën §3.2 の Čech の成分の評価。
-/
lemma additiveProductIsoPi_inv_π (i : ι) :
    (additiveProductIsoPi G).inv ≫ Pi.π G i =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i => G i) i) := by
  rw [← additiveProductIsoPi_hom_eval G i, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.DerivedGeometry
