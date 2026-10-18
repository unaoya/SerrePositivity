module
public import SerrePositivity.KST.ProExcision.RelativeBarPairs

/-!
# 基底を変える同変な単体射と半直積対

概要：作用するモノイドの変更を許す同変射から実半直積対の射を作る。
方針：二つの実自然変換と各次数の同変性を半直積の誘導写像へ渡す。
規約：KST Claim 4.15 の rank の安定化、ホモロジーの結論をデータに含めない。
使われ方：有限 rank の相対項の順序列を作る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {G H G' H' : SimplicialObject MonCat.{u}}

/-- 概要：基底を変える同変な実単体射。
方針：基底とファイバーの射、および作用の可換性を指定する。
規約：KST Claim 4.15、実代数的データだけを保持する。
使われ方：有限 rank の半直積の安定化。 -/
structure SimplicialActionOverHom (A : SimplicialMonoidAction G H)
    (B : SimplicialMonoidAction G' H') where
  base : G ⟶ G'
  fiber : H ⟶ H'
  equivariant : ∀ k (g : G.obj k) (v : H.obj k),
    (fiber.app k).hom (A.action k g v) = B.action k ((base.app k).hom g) ((fiber.app k).hom v)

/-- 概要：基底を変える同変射が誘導する半直積の実単体射。
方針：各次数の半直積の誘導射を二つの射の自然性で束ねる。
規約：KST Claim 4.15。使われ方：rank の安定化の全空間射。 -/
def SimplicialActionOverHom.total {A : SimplicialMonoidAction G H}
    {B : SimplicialMonoidAction G' H'} (f : SimplicialActionOverHom A B) :
    simplicialActionProduct A ⟶ simplicialActionProduct B where
  app k := by
    letI := A.actionStructure k
    letI := B.actionStructure k
    exact MonCat.ofHom (actionProductMap (f.base.app k).hom (f.fiber.app k).hom (f.equivariant k))
  naturality {k l} φ := by
    letI := A.actionStructure k
    letI := A.actionStructure l
    letI := B.actionStructure k
    letI := B.actionStructure l
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply ActionProduct.ext
    · exact congrArg (fun z ↦ z.hom x.base) (f.base.naturality φ)
    · exact congrArg (fun z ↦ z.hom x.fiber) (f.fiber.naturality φ)

/-- 概要：基底を変える実同変射は標準包含との可換な半直積対の射を誘導する。
方針：ファイバー射の単位保存を各次数で使う。
規約：KST Claim 4.15。使われ方：相対項の rank の安定化。 -/
def SimplicialActionOverHom.toPairMap {A : SimplicialMonoidAction G H}
    {B : SimplicialMonoidAction G' H'} (f : SimplicialActionOverHom A B) :
    SimplicialActionPairMap A B where
  base := f.base
  total := f.total
  section_comm := by
    apply NatTrans.ext
    funext k
    letI := A.actionStructure k
    letI := B.actionStructure k
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply ActionProduct.ext
    · rfl
    · exact (f.fiber.app k).hom.map_one

end SerrePositivity.KST.ProExcision
