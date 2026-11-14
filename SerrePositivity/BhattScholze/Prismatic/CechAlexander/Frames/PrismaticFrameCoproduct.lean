module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.PrismaticFrameHomotopy
public import SerrePositivity.CategoryTheory.CechNerveData
import all SerrePositivity.BhattScholze.Prismatic.Site.PrismOver

/-!
# 頂点枠の標準余積と弱始性

## 概要
頂点の変数像を指定できる prismatic 枠の各項は零次項の余積になる。
## 方針
既存の枠の延長の一意性を使い、各脚を変数で照合する。
## 規約
BS 著者版 Construction 4.17–4.18。変数の添字は剰余環全体でなくてもよい。
## 使われ方
有限 affine 模型と大きい模型の両方の Čech データ。
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
namespace SerrePositivity.BhattScholze.Prismatic.PrismOverVertexFrame
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}
variable {X : CosimplicialObject (PrismOver P R κ)} {S : Type v}
variable (D : PrismOverVertexFrame P R κ X S)

/-- 枠からの射は変数の剰余を保存する。 -/
theorem image_mod {n : ℕ} {T : PrismOver P R κ}
    (f : X.obj ⦋n⦌ ⟶ T) (x : S) (i : Fin (n + 1)) :
    Ideal.Quotient.mk T.Q.ideal (f.toHom.toRingHom (D.variableImage n x i)) =
      T.sec (D.residue x) := by
  rw [← OrientedPrism.Hom.quotientMap_mk, D.variable_mod]
  exact RingHom.congr_fun f.comm_sec _

/-- 頂点からの射をまとめた余積の降下射。 -/
def coproductDesc (n : ℕ) (T : PrismOver P R κ)
    (f : Fin (n + 1) → (X.obj ⦋0⦌ ⟶ T)) : X.obj ⦋n⦌ ⟶ T :=
  (D.lift n T (fun x i => (f i).toHom.toRingHom (D.variableImage 0 x 0))
    (fun x i => image_mod D (f i) x 0)).choose

/-- 降下射の変数上の値。 -/
theorem coproductDesc_variable (n : ℕ) (T : PrismOver P R κ)
    (f : Fin (n + 1) → (X.obj ⦋0⦌ ⟶ T)) (x : S) (i : Fin (n + 1)) :
    (D.coproductDesc n T f).toHom.toRingHom (D.variableImage n x i) =
      (f i).toHom.toRingHom (D.variableImage 0 x 0) :=
  (D.lift n T (fun x i => (f i).toHom.toRingHom (D.variableImage 0 x 0))
    (fun x i => image_mod D (f i) x 0)).choose_spec.1 x i

/-- 概要：標準頂点の脚は n 次項を零次項の n+1 個の余積にする。
方針：枠の lift と hom_ext を使う。
規約：BS 著者版 Construction 4.17。使われ方：site の Čech 脈体。 -/
def isCoproduct (n : ℕ) : IsColimit (Cofan.mk (X.obj ⦋n⦌)
    (fun i : Fin (n + 1) => X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) := by
  refine Cofan.IsColimit.mk _ (fun s => D.coproductDesc n s.pt s.inj) ?_ ?_
  · intro s i
    apply D.hom_ext
    intro x j
    change (D.coproductDesc n s.pt s.inj).toHom.toRingHom
      ((X.map _).toHom.toRingHom (D.variableImage 0 x j)) = _
    rw [D.variable_map, D.coproductDesc_variable]
    exact congrArg (fun k => (s.inj i).toHom.toRingHom (D.variableImage 0 x k))
      (by apply Fin.ext; omega)
  · intro s g hg
    apply D.hom_ext
    intro x i
    have h := congrArg (fun a : X.obj ⦋0⦌ ⟶ s.pt =>
      a.toHom.toRingHom (D.variableImage 0 x 0)) (hg i)
    change g.toHom.toRingHom ((X.map _).toHom.toRingHom (D.variableImage 0 x 0)) = _ at h
    rw [D.variable_map] at h
    exact h.trans (D.coproductDesc_variable n s.pt s.inj x i).symm

include D in
/-- 概要：枠の任意の次数の項は弱始対象。
方針：剰余構造射の値を商写像で持ち上げ、lift へ渡す。
規約：BS 著者版 Construction 4.17。使われ方：有限 affine 模型の弱終性。 -/
theorem weaklyInitial (n : ℕ) : CategoryTheory.IsWeaklyInitial (X.obj ⦋n⦌) := by
  intro T
  let z : S → Fin (n + 1) → T.B := fun x _ =>
    (Ideal.Quotient.mk_surjective (T.sec (D.residue x))).choose
  exact ⟨(D.lift n T z (fun x _ =>
    (Ideal.Quotient.mk_surjective (T.sec (D.residue x))).choose_spec)).choose⟩

/-- 枠の標準余積を反対圏の Čech データにする。 -/
def cechNerve : CategoryTheory.CechNerveData (Opposite.op (X.obj ⦋0⦌)) :=
  CategoryTheory.CechNerveData.ofCoproducts X D.isCoproduct

end SerrePositivity.BhattScholze.Prismatic.PrismOverVertexFrame
