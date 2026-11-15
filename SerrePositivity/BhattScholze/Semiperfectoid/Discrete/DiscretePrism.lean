module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import SerrePositivity.BhattScholze.Semiperfectoid.Discrete.DiscreteDelta

/-!
# 離散な環からの prism と評価射

## 概要
指定の δ 構造と完備性から向き付き prism を作る。Frobenius と可換な評価射を site の射に持ち上げる。

## 方針
基底の distinguished 元を写し、評価の終域では p の正則性を使う。

## 規約
BS 著者版 Lemma 7.7 (2), (3) の古典的な部分。評価射は p 正則な対象上で扱う。

## 使われ方
離散な環の模型と prismatic site の始対象の構成。
-/

public noncomputable section

universe u v

namespace SerrePositivity.BhattScholze.OrientedPrism

open _root_.SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {C : Type v} [CommRing C]

/-- 概要：基底の生成元の像が正則で、指定の二座標で導来完備なら、向き付き prism を得る。
方針：基底の distinguished 元を δ 射で写す。
規約：BS 著者版 Lemma 7.7 (2) の環の段階。
使われ方：指定された離散模型の prism 構造。 -/
@[expose] def ofDiscreteDelta (P : OrientedPrism p A) (D : DeltaStructure p C)
    (η : A →+* C) (hη : P.deltaStructure.IsDeltaHom D η)
    (hreg : IsRegular (η P.generator))
    (hp : IsModuleComplete C (p : C) (ModuleCat.of C C))
    (hd : IsModuleComplete C (η P.generator) (ModuleCat.of C C)) : OrientedPrism p C :=
  ofDistinguished D (η P.generator) (hη.map_isDistinguished P.isDistinguished_generator)
    hreg.left hp hd

/-- 概要：生成元で割った離散模型の p 冪ねじれが有界なら、構成した prism は有界。
方針：prism の剰余を入力の生成元による剰余と同定する。
規約：BS 著者版 Lemma 7.7 (2) の有界性。
使われ方：離散模型を有界 prismatic site の対象にする。 -/
theorem ofDiscreteDelta_bounded (P : OrientedPrism p A) (D : DeltaStructure p C)
    (η : A →+* C) (hη : P.deltaStructure.IsDeltaHom D η)
    (hreg : IsRegular (η P.generator))
    (hp : IsModuleComplete C (p : C) (ModuleCat.of C C))
    (hd : IsModuleComplete C (η P.generator) (ModuleCat.of C C))
    (hb : ∃ N : ℕ, ∀ (n : ℕ) (x : C ⧸ Ideal.span {η P.generator}),
      (p : C ⧸ Ideal.span {η P.generator}) ^ n * x = 0 →
        (p : C ⧸ Ideal.span {η P.generator}) ^ N * x = 0) :
    Prismatic.IsBoundedPrism (P.ofDiscreteDelta D η hη hreg hp hd) := hb

/-- 概要：離散模型への基底射は prism の射になる。
方針：指定の δ 射は選択された生成元をその像へ送る。
規約：BS 著者版 Lemma 7.7 (2)。
使われ方：離散模型を site の対象として読む。 -/
@[expose] def toDiscreteDelta (P : OrientedPrism p A) (D : DeltaStructure p C)
    (η : A →+* C) (hη : P.deltaStructure.IsDeltaHom D η)
    (hreg : IsRegular (η P.generator))
    (hp : IsModuleComplete C (p : C) (ModuleCat.of C C))
    (hd : IsModuleComplete C (η P.generator) (ModuleCat.of C C)) :
    Hom P (P.ofDiscreteDelta D η hη hreg hp hd) where
  toRingHom := η
  map_delta := hη
  ideal_le := by
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.subset_span (Set.mem_singleton _)

/-- 概要：p 正則な終域への Frobenius と可換な環射は、生成元の像の条件の下で prism の射になる。
方針：Frobenius の可換式から p を消去して δ 射性を得る。
規約：BS 著者版 Lemma 7.7 (3) の p 正則な対象の範囲。
使われ方：評価環射を prism の射へ移す。 -/
@[expose] def homOfFrobenius (P : OrientedPrism p A) (Q : OrientedPrism p C)
    (f : A →+* C) (hp : IsRegular (p : C))
    (hφ : f.comp P.deltaStructure.frobeniusLift = Q.deltaStructure.frobeniusLift.comp f)
    (hd : f P.generator ∈ Q.ideal) : Hom P Q where
  toRingHom := f
  map_delta := DeltaStructure.isDeltaHom_of_map_frobeniusLift f hp.left (RingHom.congr_fun hφ)
  ideal_le := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hd)

end SerrePositivity.BhattScholze.OrientedPrism

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open _root_.CategoryTheory

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

/-- 概要：基底脚と剰余上の評価脚を保つ Frobenius 可換な環射は、p 正則な終域への site の射。
方針：prism の射を構成して、二つの可換条件を付ける。
規約：BS 著者版 Lemma 7.7 (3) の古典的な評価の部分。
使われ方：自然な環の評価族を site に持ち上げる。 -/
def homOfFrobenius {X Y : PrismOver P R κ}
    (f : X.B →+* Y.B) (hp : IsRegular (p : Y.B))
    (hφ : f.comp X.Q.deltaStructure.frobeniusLift = Y.Q.deltaStructure.frobeniusLift.comp f)
    (hd : f X.Q.generator ∈ Y.Q.ideal)
    (hbase : f.comp X.toHom.toRingHom = Y.toHom.toRingHom)
    (hsec : (X.Q.homOfFrobenius Y.Q f hp hφ hd).quotientMap.comp X.sec = Y.sec) : X ⟶ Y where
  toHom := X.Q.homOfFrobenius Y.Q f hp hφ hd
  comm_base := OrientedPrism.Hom.ext hbase
  comm_sec := hsec

end SerrePositivity.BhattScholze.Prismatic.PrismOver

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 7.7" (partial := component) "BS-W15 K5（11-11）：離散な場合の δ 構造の一意性、離散な prism と Frobenius からの射、p 正則な部分圏での始性は本体。導来 prismatic コホモロジー Δ_R/A との同一視（G10、∞ 側）は drafts の A3/DiscreteCase"] _root_.SerrePositivity.BhattScholze.OrientedPrism.homOfFrobenius
attribute [cite BS19 "Lemma 7.7" (partial := component) "BS-W15 K5（11-11）：離散な場合の δ 構造の一意性、離散な prism と Frobenius からの射、p 正則な部分圏での始性は本体。導来 prismatic コホモロジー Δ_R/A との同一視（G10、∞ 側）は drafts の A3/DiscreteCase"] _root_.SerrePositivity.BhattScholze.OrientedPrism.ofDiscreteDelta
attribute [cite BS19 "Lemma 7.7" (partial := component) "BS-W15 K5（11-11）：離散な場合の δ 構造の一意性、離散な prism と Frobenius からの射、p 正則な部分圏での始性は本体。導来 prismatic コホモロジー Δ_R/A との同一視（G10、∞ 側）は drafts の A3/DiscreteCase"] _root_.SerrePositivity.BhattScholze.OrientedPrism.ofDiscreteDelta_bounded
attribute [cite BS19 "Lemma 7.7" (partial := component) "BS-W15 K5（11-11）：離散な場合の δ 構造の一意性、離散な prism と Frobenius からの射、p 正則な部分圏での始性は本体。導来 prismatic コホモロジー Δ_R/A との同一視（G10、∞ 側）は drafts の A3/DiscreteCase"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.homOfFrobenius
