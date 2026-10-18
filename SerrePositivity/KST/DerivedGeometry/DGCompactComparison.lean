module

public import SerrePositivity.KST.DerivedGeometry.AdjunctionCompact
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverse

/-!
概要：圏の余積 compact 性と既存 dg 加群の compact 性を接続する。
方針：両定義が同じ有限和分解の条件であることを使う。
規約：既存 DifferentialGraded の定義を変更しない。
使われ方：Toën §3.2、Bondal–van den Bergh Thm 3.1.1 の T1 から既存の perfect 判定。
-/

@[expose] public section

universe u v

namespace SerrePositivity.KST.DerivedGeometry

open SerrePositivity.DifferentialGraded

/--
概要：一般の余積 compact 条件は既存の dg 加群 compact 条件に一致する。
方針：指定宇宙と有限和の定義を展開する。
規約：dg 圏の smallness は既存 moduleCompact の API と一致させる。
使われ方：Toën §3.2、既存 moduleCompact_iff_perfect への接続。
-/
lemma coproductCompact_iff_moduleCompact (A : Type u) [CommRing A]
    (D : Type v) [DGCategory A D] [Small.{u} D]
    (X : DerivedModuleCategory A D) :
    coproductCompact.{u} X ↔ moduleCompact A D X := Iff.rfl

/--
概要：一般の余積 compact 条件は既存 dg 加群の perfect 条件に一致する。
方針：有限和の比較と証明済み moduleCompact_iff_perfect を合成する。
規約：有限 cell 分解の存在を追加の仮定としない。
使われ方：Toën §3.2、T1 から既存の perfect dg 加群圏への接続。
-/
lemma coproductCompact_iff_modulePerfect (A : Type u) [CommRing A]
    (D : Type v) [DGCategory A D] [Small.{u} D]
    (X : DerivedModuleCategory A D) :
    coproductCompact.{u} X ↔ modulePerfect A D X :=
  (coproductCompact_iff_moduleCompact A D X).trans (moduleCompact_iff_perfect A D X)

end SerrePositivity.KST.DerivedGeometry
