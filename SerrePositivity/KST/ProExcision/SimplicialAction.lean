module

public import SerrePositivity.KST.ProExcision.GroupHomology
public import SerrePositivity.KST.Comparison.MonoidTranslations

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# 単体的モノイドの作用と半直積

概要：一般の単体的モノイドの作用を次数ごとの準同型として与え、半直積を構成する。
方針：作用の自然性から面・退化に沿う半直積の射を作る。
規約：群状性は K-L2 の π₀ の群条件を使用する。次数ごとの群性を追加しない。
使われ方：KST Prop A.1・Lemma A.2 の半直積 bar と台写像。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
open scoped Simplicial

variable (G H : SimplicialObject MonCat.{u})

/-- 概要：単体的モノイドの単体的モノイドへの作用。
方針：各次数のモノイド準同型による作用と全単体射への自然性を指定する。
規約：作用する各元は自己同型でなく自己準同型でよい。
使われ方：KST Appendix A の群状モノイド作用の数学的なデータ。 -/
structure SimplicialMonoidAction where
  /-- 概要：次数ごとの自己準同型への作用。方針：モノイド準同型。
  規約：可逆性は不要。使われ方：KST App. A の半直積の積。 -/
  action : ∀ n : SimplexCategoryᵒᵖ, G.obj n →* Monoid.End (H.obj n)
  /-- 概要：作用は全ての単体射と可換。方針：両成分を同時に写す。
  規約：自然性は次数ごとに厳密。使われ方：KST App. A の単体的半直積。 -/
  naturality : ∀ {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (a : G.obj n) (b : H.obj n),
    (H.map f).hom (action n a b) = action m ((G.map f).hom a) ((H.map f).hom b)

variable {G H}

/-- 概要：準同型への作用を通常の乗法を保つモノイド作用として読む。
方針：自己準同型の積は写像の合成であることを使う。
規約：構造を明示引数として渡し、競合する大域インスタンスを作らない。
使われ方：KST Prop A.1 の各次数の半直積構造。 -/
@[instance_reducible] def SimplicialMonoidAction.actionStructure (A : SimplicialMonoidAction G H)
    (n : SimplexCategoryᵒᵖ) : MulDistribMulAction (G.obj n) (H.obj n) where
  smul a b := A.action n a b
  one_smul b := by
    change A.action n 1 b = b
    rw [map_one]
    rfl
  mul_smul a b c := by
    change A.action n (a * b) c = A.action n a (A.action n b c)
    rw [map_mul]
    rfl
  smul_one a := map_one _
  smul_mul a b c := map_mul _ _ _

/-- 概要：単体的作用の半直積モノイド。
方針：各次数の半直積と、作用に同変な面・退化からの誘導射を使う。
規約：G ⋉ H の順。使われ方：KST Prop A.1 の分類空間と Lemma A.2 の全空間。 -/
def simplicialActionProduct (A : SimplicialMonoidAction G H) : SimplicialObject MonCat.{u} where
  obj n := letI := A.actionStructure n; MonCat.of (ActionProduct (G.obj n) (H.obj n))
  map {n m} f := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    exact MonCat.ofHom (actionProductMap (G.map f).hom (H.map f).hom (A.naturality f))
  map_id n := by
    letI := A.actionStructure n
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply ActionProduct.ext
    · change (G.map (𝟙 n)).hom x.base = x.base
      rw [G.map_id]
      rfl
    · change (H.map (𝟙 n)).hom x.fiber = x.fiber
      rw [H.map_id]
      rfl
  map_comp {n m k} f g := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    letI := A.actionStructure k
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply ActionProduct.ext
    · change (G.map (f ≫ g)).hom x.base = (G.map g).hom ((G.map f).hom x.base)
      rw [G.map_comp]
      rfl
    · change (H.map (f ≫ g)).hom x.fiber = (H.map g).hom ((H.map f).hom x.fiber)
      rw [H.map_comp]
      rfl

/-- 概要：単体的半直積の G への射影。
方針：各次数で第一成分を取る。
規約：単体的モノイドの射。使われ方：KST App. A の分裂相対ホモロジーの射影。 -/
def simplicialActionProductProjection (A : SimplicialMonoidAction G H) :
    simplicialActionProduct A ⟶ G where
  app n := by
    letI := A.actionStructure n
    exact MonCat.ofHom actionProductProjection
  naturality _ _ _ := by rfl

/-- 概要：G の単体的半直積への標準包含。
方針：各次数で H 成分を単位にする。
規約：単体的モノイドの射。使われ方：KST App. A の相対項の基準包含。 -/
def simplicialActionProductSection (A : SimplicialMonoidAction G H) :
    G ⟶ simplicialActionProduct A where
  app n := by
    letI := A.actionStructure n
    exact MonCat.ofHom actionProductSection
  naturality n m f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply ActionProduct.ext
    · rfl
    · change 1 = (H.map f).hom 1
      exact (map_one _).symm

/-- 概要：単体的半直積の包含と射影は分裂する。
方針：各次数で既存の分裂等式を使う。
規約：単体的モノイドの射の等式。
使われ方：KST App. A の相対ホモロジーを分裂余核として扱う。 -/
@[simp] theorem simplicialActionProductSection_projection (A : SimplicialMonoidAction G H) :
    simplicialActionProductSection A ≫ simplicialActionProductProjection A = 𝟙 G := by
  rfl

/-- 概要：半直積の台単体集合上の作用写像 ψ。
方針：次数ごとの台の作用写像を作用の自然性でつなぐ。
規約：モノイド準同型としては構成しない。
使われ方：KST Lemma A.2 の ψ(g,h)=(g,g(h))。 -/
def simplicialActionProductTwist (A : SimplicialMonoidAction G H) :
    monoidSpace (simplicialActionProduct A) ⟶ monoidSpace (simplicialActionProduct A) where
  app n := by
    letI := A.actionStructure n
    exact TypeCat.ofHom actionProductTwist
  naturality n m f := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    apply ConcreteCategory.hom_ext
    intro x
    exact (actionProductTwist_natural (G.map f).hom (H.map f).hom (A.naturality f) x).symm

end SerrePositivity.KST.ProExcision
