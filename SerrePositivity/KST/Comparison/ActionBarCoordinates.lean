module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.BarSegal
public import SerrePositivity.KST.Comparison.RegularBarContraction

/-!
# 正則作用の bar の積座標

概要：正則作用の射列を、一対象圏への射影と始点の元で記述する。
方針：一対象圏の射列の始点からの射を各頂点へ作用させて持ち上げる。
規約：Segal 1974 Proposition 1.5・1.6 の bar 束の座標。
使われ方：作用によるファイバーの移送とホモトピー引き戻し性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

/--
概要：一対象圏の射列の始点から各頂点への射のラベル。
方針：順序圏の零頂点からの一意な射を評価する。
規約：Segal 1974 Proposition 1.6 の作用による移送。
使われ方：始点を指定した射列の正則作用への持ち上げ。
-/
def monoidPrefixLabel (T : MonCat.{u}) {n : ℕ} (F : (nerve (SingleObj T)) _⦋n⦌)
    (i : Fin (n + 1)) : T := F.map (homOfLE (Fin.zero_le i))

/--
概要：始点への前置ラベルは単位である。
方針：順序圏の恒等射の保存を使う。
規約：Segal 1974 Proposition 1.6 の始点の座標。
使われ方：持ち上げの始点の確認。
-/
theorem monoidPrefixLabel_zero (T : MonCat.{u}) {n : ℕ}
    (F : (nerve (SingleObj T)) _⦋n⦌) : monoidPrefixLabel T F 0 = 1 := by
  change F.map (𝟙 (0 : Fin (n + 1))) = (1 : T)
  rw [F.map_id, SingleObj.id_as_one]

/--
概要：前置ラベルは後続射のラベルの作用と可換である。
方針：零頂点からの射の合成の一意性と関手の合成保存を使う。
規約：Segal 1974 Proposition 1.6。後続ラベルは左から掛ける。
使われ方：正則作用への持ち上げの射の条件。
-/
theorem monoidPrefixLabel_map (T : MonCat.{u}) {n : ℕ}
    (F : (nerve (SingleObj T)) _⦋n⦌) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show T from F.map f) * monoidPrefixLabel T F i = monoidPrefixLabel T F j := by
  have h := F.map_comp (homOfLE (Fin.zero_le i)) f
  rw [show homOfLE (Fin.zero_le i) ≫ f = homOfLE (Fin.zero_le j) from Subsingleton.elim _ _] at h
  exact h.symm

/--
概要：射列と始点の元から正則作用の射列を構成する。
方針：各頂点を前置ラベルの作用で定め、射には元の射列のラベルを使う。
規約：Segal 1974 Proposition 1.5・1.6 の bar 束の積座標。
使われ方：各行の全空間と基底とモノイドの積との同型。
-/
def regularActionLift (T : MonCat.{u}) {n : ℕ} (F : (nerve (SingleObj T)) _⦋n⦌)
    (a : T) : (nerve (RegularAction T)) _⦋n⦌ where
  obj i := ⟨monoidPrefixLabel T F i * a⟩
  map {i j} f := ⟨F.map f, by
    change (show T from F.map f) * (monoidPrefixLabel T F i * a) = monoidPrefixLabel T F j * a
    rw [← mul_assoc, monoidPrefixLabel_map]⟩
  map_id i := by
    apply Subtype.ext
    exact (F.map_id i).trans (SingleObj.id_as_one T (F.obj i))
  map_comp f g := by
    apply Subtype.ext
    exact F.map_comp f g
/--
概要：持ち上げた正則作用の射列の始点は指定した元である。
方針：始点の前置ラベルが単位であることを使う。
規約：Segal 1974 Proposition 1.6 の全空間の積座標。
使われ方：積座標の逆写像の一方の合成。
-/
theorem regularActionLift_initial (T : MonCat.{u}) {n : ℕ}
    (F : (nerve (SingleObj T)) _⦋n⦌) (a : T) :
    (regularActionLift T F a).obj 0 = RegularAction.mk a := by
  change RegularAction.mk (monoidPrefixLabel T F 0 * a) = RegularAction.mk a
  rw [monoidPrefixLabel_zero, one_mul]

/--
概要：持ち上げた正則作用の射列を射影すると元の射列へ戻る。
方針：対象は一意であり、射のラベルは元のままであることを使う。
規約：Segal 1974 Proposition 1.6 の全空間の積分解。
使われ方：積座標の逆写像の証明。
-/
theorem regularActionLift_projection (T : MonCat.{u}) {n : ℕ}
    (F : (nerve (SingleObj T)) _⦋n⦌) (a : T) :
    regularActionLift T F a ⋙ regularActionProjection T = F := by
  refine CategoryTheory.Functor.ext (fun _ => Quiver.SingleObj.ext (α := T)) ?_
  intro i j f
  simp only [monoidSingleObj_eqToHom, SingleObj.comp_as_mul, mul_one, one_mul]
  rfl

/--
概要：正則作用の射列を射影と始点から復元すると元に戻る。
方針：各頂点で始点からの射の作用条件を使い、各射でラベルを比較する。
規約：Segal 1974 Proposition 1.6。各次数の逆元は不要。
使われ方：全空間の各行の積分解。
-/
theorem regularActionLift_reconstruct (T : MonCat.{u}) {n : ℕ}
    (E : (nerve (RegularAction T)) _⦋n⦌) :
    regularActionLift T (E ⋙ regularActionProjection T) (E.obj 0).val = E := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · exact congrArg RegularAction.mk (E.map (homOfLE (Fin.zero_le i))).property
  · intro i j f
    apply Subtype.ext
    simp only [regularAction_comp_val, regularAction_eqToHom_val, one_mul, mul_one]
    rfl

/--
概要：正則作用の射列は基底の射列と始点の元の組と全単射である。
方針：射影と始点を読み取り、前置ラベルの作用による持ち上げで復元する。
規約：Segal 1974 Proposition 1.5・1.6 の普遍 bar 束の積座標。
使われ方：全空間と基底の行ごとの積同型。
-/
def regularActionCoordinateEquiv (T : MonCat.{u}) (n : ℕ) :
    (nerve (RegularAction T)) _⦋n⦌ ≃ ((nerve (SingleObj T)) _⦋n⦌ × T) where
  toFun E := ⟨E ⋙ regularActionProjection T, (E.obj 0).val⟩
  invFun p := regularActionLift T p.1 p.2
  left_inv := regularActionLift_reconstruct T
  right_inv p := by
    apply Prod.ext
    · exact regularActionLift_projection T p.1 p.2
    · exact congrArg RegularAction.val (regularActionLift_initial T p.1 p.2)

/--
概要：正則 bar の各行は基底の行と M の直積に自然に同型である。
方針：射影と始点の積座標を準同型に関して自然に束ねる。
規約：Segal 1974 Proposition 1.6 の普遍束の各行の座標。
使われ方：行ごとの射影のファイバーと作用写像の比較。
-/
def regularBarRowIso (M : SimplicialObject MonCat.{u}) (r : ℕ) :
    (bisimplicialRegularBar M).flip.obj (op ⦋r⦌) ≅
      (bisimplicialBar M).flip.obj (op ⦋r⦌) ⊗ monoidSpace M :=
  NatIso.ofComponents (fun n => (regularActionCoordinateEquiv (M.obj n) r).toIso) (by
    intro i j f
    apply ConcreteCategory.hom_ext
    intro E
    apply Prod.ext
    · rfl
    · rfl)

/--
概要：射列を単調な頂点列に制限すると始点座標は前置ラベルで左平行移動される。
方針：新しい始点への射の正則作用の条件を読む。
規約：Segal 1974 Proposition 1.6。任意の面と退化の作用を一つの式で記述する。
使われ方：群状性によりファイバーの移送を局所化で可逆にする。
-/
theorem regularActionCoordinate_whisker (T : MonCat.{u}) {n m : ℕ}
    (E : (nerve (RegularAction T)) _⦋n⦌) (α : Fin (m + 1) ⥤ Fin (n + 1)) :
    regularActionCoordinateEquiv T m (α ⋙ E) =
      ⟨α ⋙ E ⋙ regularActionProjection T,
        monoidPrefixLabel T (E ⋙ regularActionProjection T) (α.obj 0) * (E.obj 0).val⟩ := by
  apply Prod.ext
  · rfl
  · exact (E.map (homOfLE (Fin.zero_le (α.obj 0)))).property.symm


end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.2.2.1" (partial := special) "仮定：通常のモノイド T の自分自身への正則作用（Lean は HA の X=T の場合に限る）。結論：作用圏の神経の n 単体を基底の n 単体と T の元の組に、基底の n 単体を n 個の T の元に同定する（n 単体の積座標に一致）。Lean は始点で座標を読み、HA の面・退化写像の式と一般の作用の特徴付けは含まれない。"] _root_.SerrePositivity.KST.Comparison.regularActionCoordinateEquiv
