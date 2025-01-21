use crate::{io, helpers::{ReadExt, WriteExt}};

pub trait ColumnType:
    'static + Sized + Copy + core::fmt::Debug + PartialEq + Eq + Into<Any>
{
}

/// A column with an index and type
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Column<C: ColumnType> {
    pub index: usize,
    pub column_type: C,
}

impl<C: ColumnType> Column<C> {
    // #[cfg(test)]
    pub fn new(index: usize, column_type: C) -> Self {
        Column { index, column_type }
    }

    /// Index of this column.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Type of this column.
    pub fn column_type(&self) -> &C {
        &self.column_type
    }
}

impl Column<Any> {
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_u32(self.index as u32)?;

        match self.column_type {
            Any::Fixed => {
                writer.write_u8(255)?;
            }
            Any::Instance => {
                writer.write_u8(254)?;
            }
            Any::Advice(advice) => {
                writer.write_u8(advice.phase)?;
            }
        }
        Ok(())
    }

    pub fn read<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let index = reader.read_u32()? as usize;
        let column_type = reader.read_u8()?;

        let column_type = match column_type {
            255 => Any::Fixed,
            254 => Any::Instance,
            0..=2 => Any::Advice(Advice { phase: column_type }),
            _ => return Err("Invalid phase for advice column"),
        };

        Ok(Column { index, column_type })
    }

    pub fn bytes_length() -> usize {
        5
    }
}

/// An enum over the Advice, Fixed, Instance structs
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Any {
    /// An Advice variant
    Advice(Advice),
    /// A Fixed variant
    Fixed,
    /// An Instance variant
    Instance,
}

/// An advice column
#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct Advice {
    pub(crate) phase: u8,
}

impl Default for Advice {
    fn default() -> Advice {
        Advice {
            phase: 0,
        }
    }
}

impl Advice {
    /// Returns `Advice` in given `Phase`
    pub fn new(phase: u8) -> Advice {
        Advice {
            phase
        }
    }

    /// Phase of this column
    pub fn phase(&self) -> u8 {
        self.phase
    }
}

impl core::fmt::Debug for Advice {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut debug_struct = f.debug_struct("Advice");
        // Only show advice's phase if it's not in first phase.
        if self.phase != 0 {
            debug_struct.field("phase", &self.phase);
        }
        debug_struct.finish()
    }
}

/// A fixed column
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Fixed;

/// An instance column
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Instance;


impl ColumnType for Advice {}
impl ColumnType for Fixed {}
impl ColumnType for Instance {}
impl ColumnType for Any {}

impl From<Advice> for Any {
    fn from(advice: Advice) -> Any {
        Any::Advice(advice)
    }
}

impl From<Fixed> for Any {
    fn from(_: Fixed) -> Any {
        Any::Fixed
    }
}

impl From<Instance> for Any {
    fn from(_: Instance) -> Any {
        Any::Instance
    }
}

impl From<Column<Fixed>> for Column<Any> {
    fn from(column: Column<Fixed>) -> Column<Any> {
        Column {
            index: column.index,
            column_type: Any::Fixed,
        }
    }
}

impl From<Column<Advice>> for Column<Any> {
    fn from(advice: Column<Advice>) -> Column<Any> {
        Column {
            index: advice.index(),
            column_type: Any::Advice(advice.column_type),
        }
    }
}

impl From<Column<Instance>> for Column<Any> {
    fn from(advice: Column<Instance>) -> Column<Any> {
        Column {
            index: advice.index(),
            column_type: Any::Instance,
        }
    }
}

impl TryFrom<Column<Any>> for Column<Advice> {
    type Error = &'static str;

    fn try_from(any: Column<Any>) -> Result<Self, Self::Error> {
        match any.column_type() {
            Any::Advice(advice) => Ok(Column {
                index: any.index(),
                column_type: *advice,
            }),
            _ => Err("Cannot convert into Column<Advice>"),
        }
    }
}

impl TryFrom<Column<Any>> for Column<Fixed> {
    type Error = &'static str;

    fn try_from(any: Column<Any>) -> Result<Self, Self::Error> {
        match any.column_type() {
            Any::Fixed => Ok(Column {
                index: any.index(),
                column_type: Fixed,
            }),
            _ => Err("Cannot convert into Column<Fixed>"),
        }
    }
}

impl TryFrom<Column<Any>> for Column<Instance> {
    type Error = &'static str;

    fn try_from(any: Column<Any>) -> Result<Self, Self::Error> {
        match any.column_type() {
            Any::Instance => Ok(Column {
                index: any.index(),
                column_type: Instance,
            }),
            _ => Err("Cannot convert into Column<Instance>"),
        }
    }
}
