#[derive(Debug)]
pub enum Error {
    Init(String),
    Goal(String),
    Guide(String),
    Fact(String),
    Rewrite(String),
}

impl ToString for Error {

    fn to_string(&self) -> String {
        match self {
            Error::Init(s)    => format!("⚡️ {s}"),
            Error::Goal(s)    => format!("⚡️ {s}"),
            Error::Guide(s)   => format!("⚡️ {s}"),
            Error::Fact(s)    => format!("⚡️ {s}"),
            Error::Rewrite(s) => format!("⚡️ {s}"),
        }
    }
}

pub type Res<T> = Result<T, Error>;