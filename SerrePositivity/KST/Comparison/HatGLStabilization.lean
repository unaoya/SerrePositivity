module

public import SerrePositivity.KST.Comparison.MatrixStabilization
public import SerrePositivity.KST.Comparison.DoldKanGL

/-!
# ĜL の有限 rank 間の安定化

概要：単位とのブロック和で ĜL_r から ĜL_(r+1) への単体的モノイドの射を構成する。
方針：係数環の射との可換性から、成分上の可逆性と面・退化との自然性を確認する。
規約：KST 式 (2.3)、Lemma 2.13 の安定 rank の順序列。
使われ方：安定 ĜL の実際の余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：行列の安定化は成分環への行列の写像と可換。
方針：成分環への環準同型とブロック和の自然性を使う。
規約：単体次数は q、元の rank は r。
使われ方：成分上の可逆性の安定化による保存。
-/
theorem matrixToComponents_stabilization (A : SimplicialObject RingCat.{u}) (r q : ℕ)
    (a : Matrix (Fin r) (Fin r) (A.obj (op ⦋q⦌))) :
    matrixToComponents A (r + 1) q (matrixStabilization _ r a) =
      matrixStabilization _ r (matrixToComponents A r q a) :=
  matrixStabilization_map (SimplicialRing.simplexToComponents A q) r a

/--
概要：π₀ で可逆な行列の rank を一つ増やすモノイド準同型。
方針：成分での安定化がモノイド準同型として単元を保つことを使う。
規約：元の単体次数での行列の逆元は要求しない。
使われ方：単体的モノイドの安定化の各成分。
-/
def hatGLStabilizationAt (A : SimplicialObject RingCat.{u}) (r q : ℕ) :
    hatGLSubmonoid A r q →* hatGLSubmonoid A (r + 1) q where
  toFun a := ⟨matrixStabilization _ r a.1, by
    change IsUnit (matrixToComponents A (r + 1) q (matrixStabilization _ r a.1))
    rw [matrixToComponents_stabilization]
    exact a.2.map (matrixStabilization _ r)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.1 b.1)

/--
概要：ĜL_r から ĜL_(r+1) への単体的モノイドの自然な射。
方針：各次数の安定化を取り、係数環の射との可換性で自然性を証明する。
規約：全ての面・退化と厳密に可換する。
使われ方：安定 rank の ĜL の順序列の遷移。
-/
def hatGLStabilization (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    hatGLMonoidObject A r ⟶ hatGLMonoidObject A (r + 1) where
  app q := MonCat.ofHom (hatGLStabilizationAt A r q.unop.len)
  naturality {p q} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact (matrixStabilization_map (A.map f).hom r a.1).symm

end SerrePositivity.KST.Comparison
