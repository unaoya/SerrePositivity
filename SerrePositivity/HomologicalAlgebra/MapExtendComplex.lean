module
public import SerrePositivity.HomologicalAlgebra.MapExtend

/-!
概要：既存の関手と零延長の比較を、複体の圏上の自然同型として束ねる。
方針：MapExtend の指定同型と自然性を再利用する。
規約：既存の比較射を選び直さず、元の埋め込みと関手を保持する。
使われ方：HA 1.2.4、G10 の離散加群の二重複体と交代余面複体の比較。
-/
@[expose] public noncomputable section
universe u v w z
open CategoryTheory Limits HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {D : Type w} [Category.{z} D] [Preadditive D] [HasZeroObject D]
variable (F : C ⥤ D) [F.Additive]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- 引数順を埋め込み・複体にそろえた、既存の指定比較への入口。 -/
abbrev mapExtendIso (e : c.Embedding c') (K : HomologicalComplex C c) :=
  SerrePositivity.mapExtendIso F K e

/-- 既存の比較と自然性による、複体の圏上での自然同型。 -/
def mapExtendNatIso (e : c.Embedding c') :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (mapExtendIso F e) (fun f =>
    SerrePositivity.mapExtendIso_naturality F e f)

end SerrePositivity.HomologicalAlgebra
