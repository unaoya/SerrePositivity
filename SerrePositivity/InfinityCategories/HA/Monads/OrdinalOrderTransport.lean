module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrderProfiles

/-!
概要：有限単調射の個数の等式に沿う輸送と、端点・恒等射・全合成との両立。
方針：個数を同一視して元の有限単調射へ戻す。
規約：端点の値は自然数として保持する。使われ方：Riehl–Verity Proposition 3.1.10、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの実関手の型の輸送。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：個数の等式に沿って有限単調射を移す。
方針：同じ個数に戻す。規約：新しい射の存在の仮定は置かない。
使われ方：Riehl–Verity Proposition 3.1.10 の残りの射の回収。 -/
def ordinalOrderHomTransport {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) : Fin c →o Fin d := by
  subst c
  subst d
  exact f

/-- 概要：個数の輸送は元の全射の異種等式を保持する。
方針：個数を同一視する。規約：同じ有限単調射。
使われ方：Riehl–Verity Proposition 3.1.10 の係数移送。 -/
lemma ordinalOrderHomTransport_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) : HEq (ordinalOrderHomTransport hac hbd f) f := by
  subst c
  subst d
  rfl

/-- 概要：個数の輸送は指定の端点条件を保持する。
方針：個数を同一視して元の条件を使う。規約：四Homの共通の端点条件。
使われ方：Riehl–Verity Proposition 3.1.10 の実射の回収。 -/
lemma ordinalOrderHomTransport_boundary {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (X Y : WalkingAdjunctionPoint) (f : Fin a →o Fin b)
    (hf : WalkingAdjunctionOrderBoundary X Y f) :
    WalkingAdjunctionOrderBoundary X Y (ordinalOrderHomTransport hac hbd f) := by
  subst c
  subst d
  exact hf

/-- 概要：恒等射を同じ個数の等式で輸送しても恒等射となる。
方針：個数を同一視する。規約：両端は同じ等式を使う。
使われ方：Riehl–Verity Proposition 3.1.10 の実関手の単位則。 -/
lemma ordinalOrderHomTransport_id {a c : ℕ} (hac : a = c) :
    ordinalOrderHomTransport hac hac (OrderHom.id : Fin a →o Fin a) = OrderHom.id := by
  subst c
  rfl

/-- 概要：個数の輸送は有限単調射の全合成と可換。
方針：三つの個数を同一視する。規約：中間の個数の等式も保持する。
使われ方：Riehl–Verity Proposition 3.1.10 の実関手の全合成則。 -/
lemma ordinalOrderHomTransport_comp {a b c a' b' c' : ℕ}
    (ha : a = a') (hb : b = b') (hc : c = c') (f : Fin a →o Fin b) (g : Fin b →o Fin c) :
    ordinalOrderHomTransport ha hc (g.comp f) =
      (ordinalOrderHomTransport hb hc g).comp (ordinalOrderHomTransport ha hb f) := by
  subst a'
  subst b'
  subst c'
  rfl

end SerrePositivity.InfinityCategories.HA.Monads
