module

public import SerrePositivity.BhattScholze.Andre.Transfinite.CompletedMaps
public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectoidCompletionColimit
open SerrePositivity SerrePositivity.BhattScholze.Andre.Transfinite
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {A ι : Type u} [CommRing A] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S (fun i j h ↦ f i j h)]
local notation "L" => Ring.DirectLimit S (fun i j h ↦ AlgHom.toRingHom (f i j h))
local notation "D" => _root_.DirectLimit S f
local notation "ofL" => Ring.DirectLimit.of S (fun i j h ↦ AlgHom.toRingHom (f i j h))
/-- ## 概要
環余極限モデルと代数の非交和余極限モデルの環同型を作る。
BS Thm 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
両モデルの普遍性から二つの環写像を作り、標準段射上で両合成を検証する。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
def algebraRingDirectLimitEquiv : L ≃+* D := by
  let a : L →+* D := Ring.DirectLimit.lift S (fun i j h ↦ AlgHom.toRingHom (f i j h)) D
    (_root_.DirectLimit.Ring.of S f) (fun i j h x ↦ _root_.DirectLimit.Ring.of_f h x)
  let b : D →+* L := _root_.DirectLimit.Ring.lift S f L ofL
    (fun i j h x ↦ Ring.DirectLimit.of_f h x)
  have hba : b.comp a = RingHom.id L := by
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    change b (a (ofL i x)) = _
    have ha : a (ofL i x) = _root_.DirectLimit.Ring.of S f i x := Ring.DirectLimit.lift_of ..
    rw [ha]
    rfl
  have hab : a.comp b = RingHom.id D := by
    apply _root_.DirectLimit.Ring.hom_ext
    intro i
    ext x
    change a (ofL i x) = _
    exact Ring.DirectLimit.lift_of ..
  exact
    { a with
      invFun := b
      left_inv := RingHom.congr_fun hba
      right_inv := RingHom.congr_fun hab }
/-- ## 概要
余極限モデルの比較同型は各標準段射を保つ。
BS Thm 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
実際の環余極限の持上げの計算規則を使う。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
theorem algebraRingDirectLimitEquiv_of (i : ι) (x : S i) :
    algebraRingDirectLimitEquiv S f (ofL i x) = _root_.DirectLimit.Ring.of S f i x := by
  exact Ring.DirectLimit.lift_of
    (f := fun i j h ↦ AlgHom.toRingHom (f i j h)) D (_root_.DirectLimit.Ring.of S f)
    (fun i j h x ↦ _root_.DirectLimit.Ring.of_f (G := S) (f := f) h x) i x
/-- ## 概要
代数有向系の環余極限への共通基底の標準写像を定める。
BS Thm 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
非交和代数余極限の係数写像を、明示的な比較同型の逆写像で移す。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
def algebraRingDirectLimitBaseMap : A →+* L :=
  (algebraRingDirectLimitEquiv S f).symm.toRingHom.comp (algebraMap A D)
/-- ## 概要
共通基底の余極限への標準写像は、任意の一段を経由する。
BS Thm 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
比較同型の単射性と、非交和余極限の係数写像の任意の段での表示を使う。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
theorem algebraRingDirectLimitBaseMap_eq (i : ι) (a : A) :
    algebraRingDirectLimitBaseMap S f a = ofL i (algebraMap A (S i) a) := by
  apply (algebraRingDirectLimitEquiv S f).injective
  change algebraRingDirectLimitEquiv S f
    ((algebraRingDirectLimitEquiv S f).symm (algebraMap A D a)) = _
  rw [RingEquiv.apply_symm_apply, algebraRingDirectLimitEquiv_of,
    _root_.DirectLimit.algebraMap_def (f := f) i]
  rfl
/-- ## 概要
共通基底の環余極限への標準写像から代数構造を定める。
BS Thm 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
標準環準同型の toAlgebra を使う。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
@[instance_reducible]
def algebraRingDirectLimitAlgebra : Algebra A L :=
  (algebraRingDirectLimitBaseMap S f).toAlgebra
attribute [local instance] algebraRingDirectLimitAlgebra

/-- ## 概要
環余極限への標準段射を共通基底上の代数射として実現する。
BS Thm 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
共通基底の標準写像が各段を経由する公式により係数との両立性を示す。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
def algebraRingDirectLimitOf (i : ι) : S i →ₐ[A] L :=
  { ofL i with commutes' := fun a ↦ (algebraRingDirectLimitBaseMap_eq S f i a).symm }
/-- ## 概要
固定基底上で各段が I 完全忠実平坦なら、環余極限も同じ係数作用で I 完全忠実平坦である。
BS Thm 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
余極限モデルの比較を元の係数作用について線形化し、代数余極限での保存を移す。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
theorem isCompletelyFaithfullyFlat_algebraRingDirectLimit (I : Ideal A)
    (hS : ∀ i, IsCompletelyFaithfullyFlat I (S i)) :
    IsCompletelyFaithfullyFlat I L := by
  let e := algebraRingDirectLimitEquiv S f
  let E : L ≃ₗ[A] D :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def]
        change e (algebraRingDirectLimitBaseMap S f a * x) = algebraMap A D a * e x
        rw [map_mul]
        congr 1
        exact e.apply_symm_apply _ }
  exact isCompletelyFaithfullyFlat_of_linearEquiv I E.symm
    (isCompletelyFaithfullyFlat_algebraDirectLimit S f I hS)


/-- ## 概要
両立する段ごとの代数射は、環余極限からの共通基底上の代数射を誘導する。
BS Thm 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
環余極限の持上げを作り、基底の標準写像を任意の一段を経由させて係数との両立性を示す。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
def algebraRingDirectLimitLift {B : Type u} [CommRing B] [Algebra A B]
    (t : ∀ i, S i →ₐ[A] B)
    (ht : ∀ i j h x, t j (f i j h x) = t i x) : L →ₐ[A] B := by
  let q := Ring.DirectLimit.lift S (fun i j h ↦ AlgHom.toRingHom (f i j h)) B
    (fun i ↦ (t i).toRingHom) ht
  refine { q with commutes' := ?_ }
  intro a
  obtain ⟨i⟩ := ‹Nonempty ι›
  change q (algebraRingDirectLimitBaseMap S f a) = algebraMap A B a
  rw [algebraRingDirectLimitBaseMap_eq S f i a]
  have he : q (ofL i (algebraMap A (S i) a)) = t i (algebraMap A (S i) a) :=
    Ring.DirectLimit.lift_of ..
  rw [he, AlgHom.commutes]

/-- ## 概要
余極限からの代数射は標準段射上で与えられた代数射に一致する。
BS Thm 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
実際の環余極限の持上げの計算規則を使う。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
theorem algebraRingDirectLimitLift_of {B : Type u} [CommRing B] [Algebra A B]
    (t : ∀ i, S i →ₐ[A] B) (ht : ∀ i j h x, t j (f i j h x) = t i x)
    (i : ι) (x : S i) : algebraRingDirectLimitLift S f t ht (ofL i x) = t i x := by
  exact Ring.DirectLimit.lift_of B (fun i ↦ (t i).toRingHom) ht i x
end SerrePositivity.BhattScholze.Andre.Transfinite
