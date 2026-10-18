module

public import SerrePositivity.KST.Descent.CoincidenceCenter
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# 相異なる translated section の添字

## 概要
一つの切断の群による移動の集合を添字とし、重複を除いた有限推移的な族を構成する。

## 方針
群元そのものではなく、実際の射の像の部分型を取る。作用は射への後合成とする。

## 規約
像が全体を覆うことはこの構成だけからは主張しない。幾何的推移性との接続が別に必要。

## 使われ方
論文 定理 3.1 の (3.8) の推移的添字と、相異なる切断の一致中心への次元帰納。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {G : Type u} [Group G]

/-- 概要：切断の移動の相異なる射を添字とする（論文 定理 3.1）。
方針：後合成で得る射の集合の部分型を使う。
規約：安定化群が非自明でも重複する群元を別コピーとして数えない。
使われ方：有限で推移的かつ相異なる切断族。 -/
def TranslatedSectionIndex (action : G →* Aut V) (s : B ⟶ V) :=
  {t : B ⟶ V // t ∈ Set.range (fun g : G ↦ s ≫ (action g).asIso.hom)}

/-- 概要：有限群の切断軌道は有限（論文 定理 3.1）。
方針：有限な群からの像の有限性を使う。
規約：群の忠実作用を要求しない。
使われ方：一致場所の有限和とコピーの有限非交和。 -/
instance translatedSectionIndex_finite [Finite G] (action : G →* Aut V) (s : B ⟶ V) :
    Finite (TranslatedSectionIndex action s) :=
  (Set.finite_range (fun g : G ↦ s ≫ (action g).asIso.hom)).to_subtype

/-- 概要：切断軌道の添字は非空（論文 (3.8)）。
方針：単位元による移動を指定する。
規約：基底が空の場合も射の軌道は非空。
使われ方：推移的コピー上の対角比較。 -/
instance translatedSectionIndex_nonempty (action : G →* Aut V) (s : B ⟶ V) :
    Nonempty (TranslatedSectionIndex action s) :=
  ⟨⟨_, ⟨1, rfl⟩⟩⟩

/-- 概要：相異なる切断の添字への群作用（論文 定理 3.1）。
方針：後合成と自己同型の積の向きを合わせて作用を構成する。
規約：重複を除いた部分型の上で作用の法則を証明する。
使われ方：既存の軌道正方形へ入力する添字の置換作用。 -/
instance translatedSectionIndex_mulAction (action : G →* Aut V) (s : B ⟶ V) :
    MulAction G (TranslatedSectionIndex action s) where
  smul g t := ⟨t.val ≫ (action g).asIso.hom, by
    obtain ⟨h, hh⟩ := t.property
    refine ⟨g * h, ?_⟩
    simp only [map_mul, Aut.mul_asIso, Iso.trans_hom, ← Category.assoc, hh]⟩
  one_smul t := by
    apply Subtype.ext
    change t.val ≫ (action 1).asIso.hom = t.val
    simp
  mul_smul g h t := by
    apply Subtype.ext
    change t.val ≫ (action (g * h)).asIso.hom =
      (t.val ≫ (action h).asIso.hom) ≫ (action g).asIso.hom
    simp only [map_mul, Aut.mul_asIso, Iso.trans_hom, Category.assoc]

/-- 概要：切断軌道の添字への作用は推移的（論文 (3.8)）。
方針：h による移動から k による移動へは k h⁻¹ を作用させる。
規約：切断を固定する群元の有無によらない。
使われ方：コピーの不変部分を指定対角写像で同定する。 -/
instance translatedSectionIndex_pretransitive (action : G →* Aut V) (s : B ⟶ V) :
    MulAction.IsPretransitive G (TranslatedSectionIndex action s) where
  exists_smul_eq a b := by
    obtain ⟨h, hh⟩ := a.property
    obtain ⟨k, hk⟩ := b.property
    refine ⟨k * h⁻¹, Subtype.ext ?_⟩
    change a.val ≫ (action (k * h⁻¹)).asIso.hom = b.val
    rw [← hh, ← hk, map_mul, map_inv]
    simp only [Aut.mul_asIso, Aut.inv_asIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc]

/-- 概要：添字の移動は実際の切断の後合成（論文 定理 3.1）。
方針：部分型上の作用の指定を展開する。
規約：軌道正方形が要求する等式の向きを保持する。
使われ方：既存の orbitAction への同変な族の入力。 -/
theorem translatedSection_equivariant (action : G →* Aut V) (s : B ⟶ V)
    (g : G) (t : TranslatedSectionIndex action s) :
    (g • t).val = t.val ≫ (action g).asIso.hom := rfl

/-- 概要：移動した射も同じ射の切断（論文 定理 3.1）。
方針：元の切断の恒等式と作用の基底上の不変性を使う。
規約：射の等式を使い、点の等式だけから切断性を推論しない。
使われ方：重複を除いた族を軌道正方形へ供給する。 -/
theorem translatedSection_identity (p : V ⟶ B) (s : B ⟶ V) (hs : s ≫ p = 𝟙 B)
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (t : TranslatedSectionIndex action s) : t.val ≫ p = 𝟙 B := by
  obtain ⟨g, hg⟩ := t.property
  rw [← hg, Category.assoc, over_base, hs]

/-- 概要：重複を除いた切断族は Over の射として単射（論文 定理 3.1）。
方針：充満部分圏の射の外延性から部分型の等式へ移す。
規約：スキームの点写像の単射性とは異なる。
使われ方：一致中心が真閉であることと、その次元低下。 -/
theorem translatedSection_injective (action : G →* Aut V) (s : B ⟶ V) :
    Function.Injective (fun t : TranslatedSectionIndex action s ↦ t.val.hom) := by
  intro a b h
  apply Subtype.ext
  apply ObjectProperty.hom_ext
  exact h

/-- 概要：基礎点の各ファイバーで推移的なら移動切断が全体を覆う（論文 定理 3.1）。
方針：点 y と、p(y) 上の切断の点を群元で結び、その移動した切断を選ぶ。
規約：ここでは点のファイバーの推移性を明示する。幾何ファイバーからの導出は別に必要。
使われ方：実際の軌道正方形が要求する切断の像の被覆条件。 -/
theorem translatedSection_covering (p : V ⟶ B) (s : B ⟶ V) (hs : s ≫ p = 𝟙 B)
    (action : G →* Aut V)
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y) :
    ⋃ t : TranslatedSectionIndex action s, Set.range t.val.hom.left = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  have hpoint : p.hom.left (s.hom.left (p.hom.left y)) = p.hom.left y := by
    have h := congrArg (fun k : B ⟶ B ↦ k.hom.left (p.hom.left y)) hs
    exact h
  obtain ⟨g, hg⟩ := transitive _ y hpoint
  refine Set.mem_iUnion.mpr ⟨⟨s ≫ (action g).asIso.hom, ⟨g, rfl⟩⟩, p.hom.left y, ?_⟩
  exact hg

/-- 概要：相異なる移動切断の一致中心で次元が下がる（論文 定理 3.1）。
方針：構成した族の単射性を既存の被約閉中心の次元低下へ入力する。
規約：基底の既約性・被約性と有限次元上界を明示する。
使われ方：軌道段階における真閉中心上への帰納。 -/
theorem translatedSection_center_dimension_lt_bound [Finite G] [IsSeparated V.obj.hom]
    [IsReduced B.obj.left] [IrreducibleSpace B.obj.left]
    (action : G →* Aut V) (s : B ⟶ V) (d : ℕ)
    (bound : topologicalKrullDim B.obj.left ≤ d) :
    topologicalKrullDim
      (coincidenceCenter B V.obj
        (fun t : TranslatedSectionIndex action s ↦ t.val.hom)).obj.left < d :=
  coincidenceCenter_dimension_lt_bound B V.obj _ (translatedSection_injective action s) d bound

end SerrePositivity.KST.Descent
