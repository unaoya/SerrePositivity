module
public import SerrePositivity.KST.ProExcision.ActionProductLift
public import SerrePositivity.KST.ProExcision.SimplicialAction

/-!
# 半直積からの実準同型の単体的な組み立て

概要：基底・ファイバーの単体射から作用の交換則で全空間の単体射を構成する。
方針：各次数の実準同型を、二つの射の自然性と積の保存で束ねる。
規約：KST Claim 4.15。作用する元の各次数での逆元を要求しない。
使われ方：実比較射の自然性と基底の標準包含との可換性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {G H K : SimplicialObject MonCat.{u}}

/-- 概要：作用の交換則を満たす基底・ファイバーの単体射を実半直積の単体射へ束ねる。
方針：各次数で実半直積の準同型を作り、係数射の積の保存と自然性を使う。
規約：KST Claim 4.15。使われ方：実比較射の単体的な構成。 -/
def simplicialActionProductLift (A : SimplicialMonoidAction G H) (f : G ⟶ K) (h : H ⟶ K)
    (hc : ∀ k (g : G.obj k) (x : H.obj k),
      (h.app k).hom (A.action k g x) * (f.app k).hom g =
        (f.app k).hom g * (h.app k).hom x) : simplicialActionProduct A ⟶ K where
  app k := by
    letI := A.actionStructure k
    exact MonCat.ofHom (actionProductLift (f.app k).hom (h.app k).hom (hc k))
  naturality {k l} φ := by
    letI := A.actionStructure k
    letI := A.actionStructure l
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    change (h.app l).hom ((H.map φ).hom x.fiber) * (f.app l).hom ((G.map φ).hom x.base) =
      (K.map φ).hom ((h.app k).hom x.fiber * (f.app k).hom x.base)
    rw [map_mul]
    have hf := congrArg (fun z ↦ z.hom x.base) (f.naturality φ)
    have hh := congrArg (fun z ↦ z.hom x.fiber) (h.naturality φ)
    exact congrArg₂ (· * ·) hh hf

/-- 概要：実半直積の単体的な組み立ては基底の包含上で指定の射に一致する。
方針：各次数でファイバーの単位の像を消す。
規約：KST Claim 4.15。使われ方：相対項への降下の正方形。 -/
lemma simplicialActionProductLift_section (A : SimplicialMonoidAction G H) (f : G ⟶ K) (h : H ⟶ K)
    (hc : ∀ k (g : G.obj k) (x : H.obj k),
      (h.app k).hom (A.action k g x) * (f.app k).hom g =
        (f.app k).hom g * (h.app k).hom x) :
    simplicialActionProductSection A ≫ simplicialActionProductLift A f h hc = f := by
  apply NatTrans.ext
  funext k
  letI := A.actionStructure k
  apply MonCat.hom_ext
  exact actionProductLift_section (f.app k).hom (h.app k).hom (hc k)

end SerrePositivity.KST.ProExcision
