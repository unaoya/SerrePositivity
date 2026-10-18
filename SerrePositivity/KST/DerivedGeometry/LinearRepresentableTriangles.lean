module

public import SerrePositivity.KST.DerivedGeometry.LinearRepresentableConeEvaluation
public import SerrePositivity.KST.DerivedGeometry.LinearYonedaShift
public import SerrePositivity.DifferentialGraded.Module.ConeMaps
public import SerrePositivity.KST.DerivedGeometry.TriangleComparison

/-!
概要：代表加群の標準 cone 同型が標準三角形の射と両立することを証明する。
方針：評価で具体的な写像複体の比較へ戻し、入力射の等式による輸送を照合する。
規約：標準三角形の connecting map の負号を維持する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の Mathlib 導来局所化への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CochainComplex Limits Pretriangulated
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
attribute [local instance] enrichment
variable [HasBinaryBiproducts C]

/--
概要：等しい射の cone の同一視は標準包含を保つ。
方針：射の等式で帰納して恒等の比較へ戻す。
規約：入力射の等式の証明には依存しない。
使われ方：Drinfeld §2.4、KST D4 の標準 cone の輸送。
-/
theorem coneInr_transport {X Y : CochainComplex C ℤ} {f g : X ⟶ Y} (h : f = g) :
    mappingCone.inr f ≫ eqToHom (congrArg (fun k => mappingCone k) h) = mappingCone.inr g := by
  subst g
  exact Category.comp_id _

/--
概要：等しい射の cone の同一視は connecting map を保つ。
方針：射の等式で帰納して恒等の比較へ戻す。
規約：同じ標準三角形の符号を使う。
使われ方：Drinfeld §2.4、KST D4 の標準 cone の輸送。
-/
theorem coneConnecting_transport {X Y : CochainComplex C ℤ} {f g : X ⟶ Y} (h : f = g) :
    eqToHom (congrArg (fun k => mappingCone k) h) ≫ (mappingCone.triangle g).mor₃ =
      (mappingCone.triangle f).mor₃ := by
  subst g
  exact Category.id_comp _

variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：代表加群の標準 cone 同型は標準包含を保つ。
方針：評価で入力射の輸送を消し、具体的 cone 比較の包含の式を使う。
規約：実際の標準 moduleCone と同じ比較同型を使う。
使われ方：Drinfeld §2.4、KST D4 の標準三角形の比較。
-/
theorem representableStandardConeIso_inr {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    moduleConeInr A (CochainComplex C ℤ) (representablePostcompose A f) ≫
      (representableStandardConeIso A f).hom =
      representablePostcompose A (mappingCone.inr f) := by
  apply moduleMorphism_ext
  intro T
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval,
    representableStandardConeIso_hom_eval, representablePostcompose_eval A (mappingCone.inr f) T]
  rw [← Category.assoc]
  exact (congrArg (fun z => z ≫ mappingConeComparison A T f)
    (coneInr_transport (representablePostcompose_eval A f T))).trans
      (mappingConeComparison_inr A T f)

/--
概要：代表加群の標準 cone 同型は connecting map と shift 比較に関して可換。
方針：評価で入力射の輸送を追い、具体的な connecting map の比較を使う。
規約：比較同型と shift の同型を取り替えない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の標準三角形と局所化。
-/
theorem representableStandardConeIso_connecting {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    (representableStandardConeIso A f).hom ≫
      representablePostcompose A (mappingCone.triangle f).mor₃ =
      moduleConeConnecting A (CochainComplex C ℤ) (representablePostcompose A f) ≫
        (representableShiftIso A X 1).hom := by
  apply moduleMorphism_ext
  intro T
  let E := moduleEvaluation A (CochainComplex C ℤ) T
  let e := representablePostcompose_eval A f T
  have hc : (eqToHom (congrArg (fun g => mappingCone g) e) ≫ mappingConeComparison A T f) ≫
      mappingPostcompose A T (mappingCone.triangle f).mor₃ =
      (mappingCone.triangle (E.map (representablePostcompose A f))).mor₃ ≫
        mappingShiftMap A T X 1 :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => eqToHom (congrArg (fun g => mappingCone g) e) ≫ z)
        (mappingConeComparison_connecting A T f)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ mappingShiftMap A T X 1) (coneConnecting_transport e))))
  have hl := (E.map_comp (representableStandardConeIso A f).hom
    (representablePostcompose A (mappingCone.triangle f).mor₃)).trans
      (congrArg₂ (fun u v => u ≫ v) (representableStandardConeIso_hom_eval A f T)
        (representablePostcompose_eval A (mappingCone.triangle f).mor₃ T))
  have hr := (E.map_comp
    (moduleConeConnecting A (CochainComplex C ℤ) (representablePostcompose A f))
    (representableShiftIso A X 1).hom).trans
      (congrArg₂ (fun u v => u ≫ v) (moduleConeConnecting_eval A _ _ T)
        (representableShiftIso_hom_eval A X T 1))
  exact hl.trans (hc.trans hr.symm)

/--
概要：代表加群関手は元の標準 cone 三角形を標準 moduleCone 三角形へ送る。
方針：二つの恒等同型と cone の同型を、包含・connecting map の比較で束ねる。
規約：対象の同型だけで三角形の同型を仮定しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 のホモトピー圏での完全性。
-/
def complexYonedaConeTriangle (X Y : CochainComplex C ℤ) (f : X ⟶ Y) :
    Triangle (ModuleCategory A (CochainComplex C ℤ)) :=
  Triangle.mk (representablePostcompose A f) (representablePostcompose A (mappingCone.inr f))
    (representablePostcompose A (mappingCone.triangle f).mor₃ ≫ (representableShiftIso A X 1).inv)

/--
概要：明示した代表加群の三角形は同じ関手による標準三角形の像。
方針：関手の射成分と shift 比較の定義を読む。
規約：三角形の構造全体の展開を各射の証明で繰り返さない。
使われ方：Drinfeld §2.4、KST D4 の標準三角形の比較。
-/
theorem complexYonedaConeTriangle_eq {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    complexYonedaConeTriangle A X Y f =
      (complexYoneda A).mapTriangle.obj (mappingCone.triangle f) := rfl

/--
概要：標準 moduleCone 三角形と明示した代表加群三角形の同型。
方針：既に証明した包含と connecting map の式を使う。
規約：同じ標準 cone の同型を保持する。
使われ方：Drinfeld §2.4、KST D4 の三角形の比較。
-/
def representableConeTriangleIso {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    moduleConeTriangle A (CochainComplex C ℤ) (representablePostcompose A f) ≅
      complexYonedaConeTriangle A X Y f :=
  triangleIsoOfComparison (representablePostcompose A f)
    (moduleConeInr A (CochainComplex C ℤ) (representablePostcompose A f))
    (moduleConeConnecting A (CochainComplex C ℤ) (representablePostcompose A f))
    (representablePostcompose A (mappingCone.inr f))
    (representablePostcompose A (mappingCone.triangle f).mor₃)
    (representableStandardConeIso A f) (representableShiftIso A X 1)
    (representableStandardConeIso_inr A f) (representableStandardConeIso_connecting A f)

/--
概要：代表加群関手は元の標準 cone 三角形を標準 moduleCone 三角形へ送る。
方針：明示した三角形の同型を同じ関手の像との等式で移す。
規約：三角形の同型の存在を仮定しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の distinguished triangle の保存。
-/
def complexYonedaConeTriangleIso {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    moduleConeTriangle A (CochainComplex C ℤ) (representablePostcompose A f) ≅
      (complexYoneda A).mapTriangle.obj (mappingCone.triangle f) :=
  representableConeTriangleIso A f ≪≫ eqToIso (complexYonedaConeTriangle_eq A f)

end SerrePositivity.KST.DerivedGeometry.LinearComplex
