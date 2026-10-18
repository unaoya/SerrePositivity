module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
概要：非有界複体を各項 injective な contractible 複体へ単射に埋め込む構成の各項。
方針：隣接する二つの injective 埋め込みの双積を取り、第二成分から次の第一成分へ微分する。
規約：十分な injective を持つ任意のアーベル圏。有界性は不要。
使われ方：Stacks Lemma 19.12.5 (079N)、TT §3・§8、Toën §3.2 の非有界分解の構成部品。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]

/--
概要：対象族の隣接双積から作る複体。
方針：微分は第二成分を次の第一成分へ送る。
規約：添字の一致には選ばれた等式の射を使う。
使われ方：Stacks Lemma 19.12.5、TT §3 の contractible 埋め込み。
-/
def adjacentBiproductComplex (I : ℤ → C) : CochainComplex C ℤ where
  X n := I n ⊞ I (n + 1)
  d i j := if h : i + 1 = j then
      biprod.snd ≫ eqToHom (congrArg I h) ≫ biprod.inl else 0
  shape i j h := dite_eq_right (by exact h)
  d_comp_d' i j k hij hjk := by
    have hi : i + 1 = j := hij
    subst j
    have hk : (i + 1) + 1 = k := hjk
    subst k
    simp [Category.assoc]

/--
概要：複体の各項の injective 埋め込みから作る隣接双積複体。
方針：各次数の既存の injective 対象を選ぶ。
規約：まだ準同型な分解と同一視しない。
使われ方：Stacks Lemma 19.12.5、TT §3・§8 の非有界分解の最初の構成。
-/
def termInjectiveEnvelope [EnoughInjectives C] (K : CochainComplex C ℤ) : CochainComplex C ℤ :=
  adjacentBiproductComplex (fun n => Injective.under (K.X n))

/--
概要：隣接 injective 双積複体の全ての項は injective。
方針：有限双積での injectivity を使う。
規約：この条件だけから K-injectivity を結論しない。
使われ方：Stacks Lemma 19.12.5、Toën §3.2 の各項の injective 因子化。
-/
instance termInjectiveEnvelope_injective [EnoughInjectives C] (K : CochainComplex C ℤ) (n : ℤ) :
    Injective ((termInjectiveEnvelope K).X n) := by
  change Injective (Injective.under (K.X n) ⊞ Injective.under (K.X (n + 1)))
  infer_instance

/--
概要：元の複体から各項 injective な隣接双積複体への標準の鎖写像。
方針：第一成分は injective 埋め込み、第二成分は微分の後の injective 埋め込み。
規約：元の微分を保持する。
使われ方：Stacks Lemma 19.12.5、TT §3 の非有界分解の単射。
-/
def termInjectiveEnvelopeι [EnoughInjectives C] (K : CochainComplex C ℤ) :
    K ⟶ termInjectiveEnvelope K where
  f n := biprod.lift (Injective.ι (K.X n)) (K.d n (n + 1) ≫ Injective.ι (K.X (n + 1)))
  comm' i j hij := by
    have h : i + 1 = j := hij
    subst j
    dsimp [termInjectiveEnvelope, adjacentBiproductComplex]
    ext <;> simp [Category.assoc]

/--
概要：標準の鎖写像は各次数で単射。
方針：第一成分への射影との合成が元の injective 埋め込みであることを使う。
規約：複体の有界性は不要。
使われ方：Stacks Lemma 19.12.5、TT §3・§8 の余核複体の構成。
-/
instance termInjectiveEnvelopeι_f_mono [EnoughInjectives C] (K : CochainComplex C ℤ) (n : ℤ) :
    Mono ((termInjectiveEnvelopeι K).f n) := by
  have : Mono ((termInjectiveEnvelopeι K).f n ≫ biprod.fst) := by
    change Mono (biprod.lift (Injective.ι (K.X n))
      (K.d n (n + 1) ≫ Injective.ι (K.X (n + 1))) ≫ biprod.fst)
    rw [biprod.lift_fst]
    infer_instance
  exact mono_of_mono ((termInjectiveEnvelopeι K).f n) biprod.fst

/--
概要：injective 双積複体への標準の鎖写像は複体の圏でも単射。
方針：各次数の単射性から鎖写像の単射性を得る。
規約：非有界複体。
使われ方：Stacks Lemma 19.12.5、TT §3 の余核複体の構成。
-/
instance termInjectiveEnvelopeι_mono [EnoughInjectives C] (K : CochainComplex C ℤ) :
    Mono (termInjectiveEnvelopeι K) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)

end SerrePositivity.KST.DerivedGeometry
