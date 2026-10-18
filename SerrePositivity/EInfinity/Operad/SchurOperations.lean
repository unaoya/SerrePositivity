module

public import SerrePositivity.EInfinity.Operad.Schur

/-!
# Schur 対象からの射と等変な演算族

概要：Berger–Moerdijk §1 の coinvariant 表示の普遍性を arity ごとの射で記述する。
方針：有限全単射の骨格の全対象を標準有限集合として扱い、余錐を構成する。
規約：arity 0 を含み、置換は係数と入力に同時に作用する。
使われ方：自由代数の射と、代数の作用を Schur 対象からの射に束ねるために用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：同時置換に関して等変な arity ごとの演算族（Berger–Moerdijk §1）。
方針：各 arity の chain map と、coinvariant に降りるための関係式を記録する。
規約：演算に合成則や単位則はまだ要求しない。
使われ方：Schur 対象からの射の普遍性を表す。 -/
@[ext]
structure SchurOperationFamily (P : SymmetricSequence (Complex A)) (K Y : Complex A) where
  /-- 概要：arity n の演算の chain map（Berger–Moerdijk §1）。
  方針：係数複体と入力のテンソル冪からの射を指定する。
  規約：arity 0 も含める。
  使われ方：Schur 対象からの射の生成射上の値となる。 -/
  app (n : ℕ) : SymmetricSequence.level P n ⊗ power K n ⟶ Y
  /-- 概要：同時置換による coinvariant の関係式（Berger–Moerdijk §1）。
  方針：係数と入力を同じ置換で動かしても演算が変わらないことを要求する。
  規約：入力側には既存の Koszul 対称性を用いる。
  使われ方：演算族を有限全単射の図式の余錐へ束ねる。 -/
  equivariance (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (P.map (FiniteBijection.permutation n σ) ⊗ₘ (permutationAction K n σ).asIso.hom) ≫
      app n = app n

namespace SchurOperationFamily

variable {P : SymmetricSequence (Complex A)} {K Y : Complex A}

/-- 概要：arity ごとの等変な演算族の余錐（Berger–Moerdijk §1）。
方針：有限全単射の骨格の対象を自然数で展開して演算族を用いる。
規約：骨格の異なる対象間には射がないことを利用する。
使われ方：Schur 対象からの誘導射を構成する。 -/
def cocone (f : SchurOperationFamily P K Y) : Cocone (schurDiagram A P K) where
  pt := Y
  ι := {
    app := fun S => by
      rcases S with ⟨⟨n⟩⟩
      exact f.app n
    naturality := fun {S T} σ => by
      cases FiniteBijection.object_eq_of_hom σ
      rcases S with ⟨⟨n⟩⟩
      have hs : σ = FiniteBijection.permutation n (FiniteBijection.equivOfHom σ) :=
        (FiniteBijection.homOfEquiv_equivOfHom σ).symm
      change (schurDiagram A P K).map σ ≫ f.app n = f.app n ≫ 𝟙 Y
      rw [hs, Category.comp_id]
      simpa only [schurDiagram, bijectionFunctor_map_permutation] using
        f.equivariance n (FiniteBijection.equivOfHom σ) }

/-- 概要：等変な演算族から Schur 対象からの射を得る（Berger–Moerdijk §1）。
方針：構成した余錐の余極限からの降下射を取る。
規約：coinvariant の代表元を選択しない。
使われ方：自由代数からの射と代数の評価射を構成する。 -/
def desc (f : SchurOperationFamily P K Y) : (schurFunctor A P).obj K ⟶ Y :=
  colimit.desc (schurDiagram A P K) f.cocone

/-- 概要：降下射は各 arity の演算と一致する（Berger–Moerdijk §1）。
方針：余極限の構造射と降下射の合成則を用いる。
規約：標準有限集合で余錐を評価する。
使われ方：Schur の普遍性の逆写像を検証する。 -/
@[reassoc]
lemma ι_desc (f : SchurOperationFamily P K Y) (n : ℕ) :
    schurι A P K n ≫ f.desc = f.app n :=
  colimit.ι_desc _ _

end SchurOperationFamily

/-- 概要：Schur 対象からの射と等変な演算族の間の同値（Berger–Moerdijk §1）。
方針：生成射による制限と余極限からの降下が互いに逆であることを示す。
規約：合成則を要求しない演算族の段階での普遍性である。
使われ方：自由代数の随伴の Hom 対応を構成するために用いる。 -/
def schurHomEquiv (P : SymmetricSequence (Complex A)) (K Y : Complex A) :
    ((schurFunctor A P).obj K ⟶ Y) ≃ SchurOperationFamily P K Y where
  toFun f := {
    app n := schurι A P K n ≫ f
    equivariance n σ := by rw [← Category.assoc, schurι_diagonal] }
  invFun f := f.desc
  left_inv f := by
    apply schur_hom_ext A P K Y
    intro n
    exact SchurOperationFamily.ι_desc _ n
  right_inv f := by
    apply SchurOperationFamily.ext
    funext n
    exact SchurOperationFamily.ι_desc f n

end SerrePositivity.EInfinity
