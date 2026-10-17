module

public import SerrePositivity.EInfinity.Operad.TensorNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# 対称列の Schur 関手

概要：Berger–Moerdijk §1 の自由代数の底 `⊕ₙ (P(n) ⊗ K^⊗n)_{Σₙ}` を構成する。
方針：有限全単射の亜群上の余極限として、直和と coinvariant を同時に実現する。
規約：対称列の左作用を逆元で右作用に直す。テンソル作用は Koszul 符号を含む。
使われ方：オペラッドの自由代数の構造写像と普遍性を構成するための底となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：対称列と反復テンソルの同時作用の図式（Berger–Moerdijk §1）。
方針：各有限集合で `P(n) ⊗ K^⊗n` を取り、両因子の置換をテンソルする。
規約：右作用を逆元で左作用へ直した後の diagonal action に対応する。
使われ方：Schur 関手をこの図式の余極限として定義する。 -/
def schurDiagram (P : SymmetricSequence (Complex A)) (K : Complex A) :
    FiniteBijection ⥤ Complex A where
  obj S := P.obj S ⊗ (bijectionFunctor K).obj S
  map σ := P.map σ ⊗ₘ (bijectionFunctor K).map σ
  map_id S := by simp only [P.map_id, (bijectionFunctor K).map_id, tensorHom_id, id_whiskerRight]
  map_comp σ τ := by
    rw [P.map_comp, (bijectionFunctor K).map_comp, tensorHom_comp_tensorHom]

/-- 概要：複体射が誘導する Schur 図式の射（Berger–Moerdijk §1）。
方針：係数対称列を固定し、テンソル冪の射を各 arity で用いる。
規約：自然性は全置換に対するテンソル冪の自然性から得る。
使われ方：Schur 関手を複体射に作用させる。 -/
def schurDiagramMap (P : SymmetricSequence (Complex A)) {K L : Complex A} (f : K ⟶ L) :
    schurDiagram A P K ⟶ schurDiagram A P L where
  app S := 𝟙 (P.obj S) ⊗ₘ TensorPowers.map f (FiniteBijection.card S)
  naturality {S T} σ := by
    change (P.map σ ⊗ₘ (bijectionFunctor K).map σ) ≫
      (𝟙 (P.obj T) ⊗ₘ TensorPowers.map f T.card) =
        (𝟙 (P.obj S) ⊗ₘ TensorPowers.map f S.card) ≫
          (P.map σ ⊗ₘ (bijectionFunctor L).map σ)
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    rw [tensorPower_bijection_naturality]

/-- 概要：Schur 図式は底の複体に関して関手的（Berger–Moerdijk §1）。
方針：各 arity でテンソル冪の恒等射と合成則を適用する。
規約：余極限を取る前の図式圏を値域とする。
使われ方：余極限関手との合成で Schur 関手を得る。 -/
def schurDiagramFunctor (P : SymmetricSequence (Complex A)) :
    Complex A ⥤ (FiniteBijection ⥤ Complex A) where
  obj K := schurDiagram A P K
  map f := schurDiagramMap A P f
  map_id K := by
    apply NatTrans.ext
    funext S
    change (𝟙 (P.obj S) ⊗ₘ TensorPowers.map (𝟙 K) S.card) =
      𝟙 (P.obj S ⊗ power K S.card)
    rw [TensorPowers.map_id, tensorHom_id, id_whiskerRight]
  map_comp f g := by
    apply NatTrans.ext
    funext S
    simp only [schurDiagramMap, TensorPowers.map_comp, NatTrans.comp_app,
      tensorHom_comp_tensorHom, Category.id_comp]

/-- 概要：対称列 P の Schur 関手（Berger–Moerdijk §1）。
方針：`P(n) ⊗ K^⊗n` の diagonal action の余極限を取る。
規約：arity 0 を含める。オペラッドの合成則はこの定義に仮定しない。
使われ方：自由 P 代数の底の複体となる。 -/
def schurFunctor (P : SymmetricSequence (Complex A)) : Complex A ⥤ Complex A :=
  schurDiagramFunctor A P ⋙ colim

/-- 概要：各 arity のテンソルから Schur 関手への標準射（Berger–Moerdijk §1）。
方針：余極限の構造射を標準有限集合で評価する。
規約：射は coinvariant への商と直和への包含の合成を表す。
使われ方：自由代数の演算とその射を生成元上で指定する。 -/
def schurι (P : SymmetricSequence (Complex A)) (K : Complex A) (n : ℕ) :
    SymmetricSequence.level P n ⊗ power K n ⟶ (schurFunctor A P).obj K :=
  colimit.ι (schurDiagram A P K) (FiniteBijection.of n)

/-- 概要：Schur 生成射は両因子の同時置換で変わらない（Berger–Moerdijk §1）。
方針：余極限の可換性を標準置換に適用する。
規約：係数の左作用は、右作用に直す際の逆元を含む。
使われ方：自由代数の coinvariant 関係を確認する。 -/
lemma schurι_diagonal (P : SymmetricSequence (Complex A)) (K : Complex A) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (P.map (FiniteBijection.permutation n σ) ⊗ₘ (permutationAction K n σ).asIso.hom) ≫
      schurι A P K n = schurι A P K n := by
  have h := colimit.w (schurDiagram A P K) (FiniteBijection.permutation n σ)
  simpa only [schurDiagram, schurι, bijectionFunctor_map_permutation] using h

/-- 概要：Schur 生成射は底の複体射に関して自然（Berger–Moerdijk §1）。
方針：余極限に誘導される射の構造射上の等式を用いる。
規約：係数対称列 P は固定する。
使われ方：自由代数の随伴の自然性を生成元上で示す。 -/
@[reassoc]
lemma schurι_naturality (P : SymmetricSequence (Complex A)) {K L : Complex A}
    (f : K ⟶ L) (n : ℕ) :
    schurι A P K n ≫ (schurFunctor A P).map f =
      (𝟙 (SymmetricSequence.level P n) ⊗ₘ TensorPowers.map f n) ≫ schurι A P L n :=
  colimit.ι_map (schurDiagramMap A P f) (FiniteBijection.of n)

/-- 概要：Schur 対象からの射は全 arity の生成射上で決まる（Berger–Moerdijk §1）。
方針：有限全単射の骨格の各対象が標準有限集合であることを使う。
規約：coinvariant の元を選択せず、余極限の普遍性で示す。
使われ方：自由代数の射の一意性と随伴の単位・余単位の等式を示す。 -/
@[ext]
lemma schur_hom_ext (P : SymmetricSequence (Complex A)) (K Y : Complex A)
    (f g : (schurFunctor A P).obj K ⟶ Y)
    (h : ∀ n : ℕ, schurι A P K n ≫ f = schurι A P K n ≫ g) : f = g := by
  apply colimit.hom_ext
  intro S
  have hs := h (FiniteBijection.card S)
  change colimit.ι (schurDiagram A P K) (FiniteBijection.of S.card) ≫ f =
    colimit.ι (schurDiagram A P K) (FiniteBijection.of S.card) ≫ g at hs
  rw [FiniteBijection.of_card] at hs
  exact hs

/-- 概要：同時置換と両立する射族は Schur 対象からの射へ一意に降りる（Berger–Moerdijk §1）。
方針：射族を余錐に束ね、余極限の普遍性を適用する。
規約：等変性は図式の全ての全単射について要求する。
使われ方：自由代数からの代数射を生成元で定める。 -/
def schurDesc (P : SymmetricSequence (Complex A)) (K Y : Complex A)
    (f : ∀ S : FiniteBijection, (schurDiagram A P K).obj S ⟶ Y)
    (hf : ∀ {S T : FiniteBijection} (σ : S ⟶ T),
      (schurDiagram A P K).map σ ≫ f T = f S) : (schurFunctor A P).obj K ⟶ Y :=
  colimit.desc (schurDiagram A P K) {
    pt := Y
    ι := {
      app := f
      naturality := fun {S T} σ => by
        change (schurDiagram A P K).map σ ≫ f T = f S ≫ 𝟙 Y
        rw [Category.comp_id]
        exact hf σ } }

/-- 概要：Schur 対象から誘導した射は指定した生成射族に一致する（Berger–Moerdijk §1）。
方針：余極限の構造射と desc の合成則を用いる。
規約：各 arity の代表元の選択に依存しない。
使われ方：自由・忘却随伴の Hom 対応の逆写像を検証する。 -/
@[reassoc]
lemma schurι_desc (P : SymmetricSequence (Complex A)) (K Y : Complex A)
    (f : ∀ S : FiniteBijection, (schurDiagram A P K).obj S ⟶ Y)
    (hf : ∀ {S T : FiniteBijection} (σ : S ⟶ T),
      (schurDiagram A P K).map σ ≫ f T = f S) (n : ℕ) :
    schurι A P K n ≫ schurDesc A P K Y f hf = f (FiniteBijection.of n) :=
  colimit.ι_desc _ _

end SerrePositivity.EInfinity
